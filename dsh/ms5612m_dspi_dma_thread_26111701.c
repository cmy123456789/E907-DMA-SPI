/*
 * ms5612m_dspi_3.c  —  T153 / E907  MS5612M 双线 SPI + DMA 连续输出  (v3)
 * ============================================================================
 *
 * v3 新增：末尾帧循环发送（对应 XMind「末尾帧循环发送 prior1」）
 * -----------------------------------------------------------------
 *   需求：当本次数据发送完成后，如果没有新的数据，
 *         要循环发送旧数据中的「最后一帧」，以保持 MS5612M 的 DAC
 *         输出一个确定的电压。
 *
 *   实现：TC 中断里发现没有 pending 批次时，把描述符从
 *         「整个当前缓冲」改成「当前缓冲的最后 10 字节（X帧+Y帧）」，
 *         并把 MBC 改成 10。之后每个 TC 都重复这一对，
 *         DAC 就稳定停在最后一个位置，而不是重新走一遍整条轨迹。
 *
 *   状态机：
 *       正常批 ──(无新数据)──> 保持态 ──(重复最后一对)──> 保持态
 *          ^                      │
 *          └────(submit 到来)──────┘
 *
 * v3 同时修改：演示波形从锯齿改成三角波
 * -----------------------------------------------------------------
 *   v2 用 (t*7)&0xFFF / (t*3)&0xFFF，是锯齿波，每 4096 点从 4095 瞬跳回 0，
 *   两轴速率不同会画成李萨如，看起来"很奇怪"，而且振镜会被命令瞬间飞过半幅。
 *   改成三角波后无瞬跳，接线和波形都更直观。
 *   想回到锯齿把 DSPI_DEMO_MODE 改成 DSPI_DEMO_SAWTOOTH。
 *
 * 后续步骤（尚未实现）
 * --------------------
 *   step4 DMA 双缓冲：进一步压缩批次间隙
 *
 * 硬件连接
 * --------
 *   SPI1_CS0 (PK2)  → 悬空或接 MS5612M CS
 *   SPI1_CLK (PK3)  → SCLK
 *   SPI1_MOSI(PK4)  → DIN   (D0)
 *   SPI1_MISO(PK5)  → FS    (D1)
 *   MS5612M CS      → GND
 */

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include "FreeRTOS.h"
#include "task.h"

#include <hal_gpio.h>
#include <hal_timer.h>
#include <hal_thread.h>
#include <hal_clk.h>
#include <hal_spi.h>
#include <hal_reset.h>
#include <hal_interrupt.h>
#include <hal_dma.h>

/* ==========================================================================
 * 配置区
 * ========================================================================== */

#define DSPI_PORT            1u
#define DSPI_SPI_IRQ         SUNXI_IRQ_SPI1
#define DSPI_DRQ_TX          DRQDST_SPI1_TX            /* = 23 */

#define DSPI_DMA_CTRL        DMA1
#define DSPI_DMA_CHAN        DMA1_CHANNEL1

#define DSPI_GPIO_PORT       SUNXI_GPIO_K
#define DSPI_GPIO_FUNC       GPK_SPI1
#define DSPI_GPIO_PINS       (PIN_2 | PIN_3 | PIN_4 | PIN_5 | PIN_6 | PIN_7)

/* 目标 SCLK：24MHz 只能整数分频（1/2/3/4/6/8/12M）；
 * 20MHz 需要 PLL_PERI0_200M ÷ 10，本文件自动选路。 */
#define DSPI_SCLK_HZ         2000000u

/* 单批最大点数（1 点 = 1 组 X+Y = 10 字节） */
#define DSPI_PAIRS           2000u
#define DSPI_FRAME_BYTES     5u
#define DSPI_PAIR_BYTES      (DSPI_FRAME_BYTES * 2u)
#define DSPI_BUF_BYTES       (DSPI_PAIRS * DSPI_PAIR_BYTES)

/* 启动时的初始批次 */
#define DSPI_INIT_PAIRS      100u

/* DMA 的 CCU 时钟/复位（v2 起加回；链接报错时改 0） */
#define DSPI_USE_DMA_CLK_INIT 1

/* 每秒打印一次运行状态 */
#define DSPI_ENABLE_STAT     1

/* 演示波形 */
#define DSPI_DEMO_SAWTOOTH   0      /* 锯齿：瞬跳回扫，示波器好看，振镜勿用 */
#define DSPI_DEMO_TRIANGLE   1      /* 三角：无瞬跳，可直接接振镜 */
#define DSPI_DEMO_SIN_COS   2 
#define DSPI_DEMO_MODE       DSPI_DEMO_SIN_COS

/* ==========================================================================
 * 内部数据
 * ========================================================================== */

static __nocache uint8_t s_buf[2][DSPI_BUF_BYTES] __attribute__((aligned(64)));

/* 自建描述符（__nocache，运行时可随时改，DMA 立刻读到新值） */
static __nocache dma_descriptor s_desc;
static uint32_t s_desc_addr;

static dma_stream s_stream;
static dma_init_t s_dma_cfg;

static volatile uint32_t s_active;       /* 当前正在发送的缓冲索引 */
static volatile uint32_t s_cur_len;      /* 当前批次字节数 */
static volatile uint32_t s_pending_len;  /* 待切换批次的字节数 */
static volatile bool     s_pending_ready;
static volatile bool     s_hold_mode;    /* ★ v3：是否处于"末尾帧保持"状态 */

static volatile uint32_t s_tc_cnt;       /* TC 中断次数 */
static volatile uint32_t s_switch_cnt;   /* 成功换批次数 */
static volatile uint32_t s_hold_enter_cnt; /* 进入保持模式的次数 */
static volatile uint32_t s_repeat_cnt;   /* 保持态重复最后一对的次数 */
static volatile uint32_t s_busy_cnt;     /* submit 返回 -2 的次数 */
static volatile uint32_t s_stall_cnt;    /* 重装时 FIFO 一直空 */
static volatile uint32_t s_err_cnt;      /* FIFO 异常中断次数 */

/* 演示用数据 */
static uint16_t s_dx[DSPI_PAIRS];
static uint16_t s_dy[DSPI_PAIRS];

/* ==========================================================================
 * 帧编码
 * ========================================================================== */

/* 12bit 数据 + 帧头 → 32bit 编码字（偶数位 → D0） */
static uint32_t dspi_enc_word(uint16_t value, bool dac_b)
{
    uint32_t w = 0;
    int i;

    for (i = 0; i <= 22; i += 2)
        w |= ((uint32_t)((value >> (i >> 1)) & 1u)) << i;

    w |= (1u << 24);                        /* SPD = 1 */

    if (dac_b)
        w |= (1u << 28);                    /* A0 = 1 → DAC-B */

    return w;
}

/* 32bit 编码字 → 5 字节线上数据（首字节是 FS 高电平） */
static void dspi_enc_frame(uint8_t *out, uint32_t w)
{
    out[0] = 0xAAu;                         /* D0=0000, D1=1111 → FS 高 4 拍 */
    out[1] = (uint8_t)(w >> 24);
    out[2] = (uint8_t)(w >> 16);
    out[3] = (uint8_t)(w >>  8);
    out[4] = (uint8_t)(w);
}

/* 把 n 个点（每个点 = X 帧 + Y 帧）编码进 out，返回字节数 */
static uint32_t dspi_encode_pairs(uint8_t *out, const uint16_t *x,
                                  const uint16_t *y, uint32_t n)
{
    uint32_t i;

    for (i = 0; i < n; i++) {
        uint8_t *p = out + i * DSPI_PAIR_BYTES;

        dspi_enc_frame(p, dspi_enc_word(x[i], false));
        dspi_enc_frame(p + DSPI_FRAME_BYTES, dspi_enc_word(y[i], true));
    }

    return n * DSPI_PAIR_BYTES;
}

/* ==========================================================================
 * 外设强制复位
 * ========================================================================== */

static void dspi_hw_reset(void)
{
    uint32_t base  = SPI_BASE(DSPI_PORT);
    uint32_t dbase = DMAC_BASE_ADDR(DSPI_DMA_CTRL);
    uint32_t ch    = DSPI_DMA_CHAN;
    uint32_t gc;
    int t;

    hal_writel(0,    DMA_EN_REG(dbase, ch));
    hal_writel(0x3F, DMA_IRQ_PEND_REG(dbase, ch));
    hal_writel(0,    DMA_IRQ_EN_REG(dbase, ch));

    hal_spi_disable_dma_irq(DSPI_PORT, SUNXI_SPI_FIFO_CTL_TX_DRQ_EN);

    /* 必须先清 XCH，否则后面写 MBC/MTC 全部无效 */
    hal_writel(hal_readl(base + SUNXI_SPI_TC_REG) & ~SUNXI_SPI_TC_XCH,
               base + SUNXI_SPI_TC_REG);

    hal_writel(0,          base + SUNXI_SPI_INT_CTL_REG);
    hal_writel(0xFFFFFFFF, base + SUNXI_SPI_INT_STA_REG);

    hal_spi_reset_txfifo(DSPI_PORT);
    hal_spi_reset_rxfifo(DSPI_PORT);

    gc = hal_readl(base + SUNXI_SPI_GC_REG);
    hal_writel(gc | SUNXI_SPI_GC_SRST, base + SUNXI_SPI_GC_REG);

    for (t = 0; t < 100; t++) {
        udelay(10);
        if (!(hal_readl(base + SUNXI_SPI_GC_REG) & SUNXI_SPI_GC_SRST))
            break;
    }
    if (t >= 100)
        printf("[dspi] warn: soft reset timeout\n");

    printf("[dspi] hw reset done\n");
}

/* ==========================================================================
 * DMA 的 CCU 时钟 / 复位
 * ========================================================================== */

static void dspi_dma_clk_init(void)
{
#if DSPI_USE_DMA_CLK_INIT
    extern int hal_dma_reset_set(uint32_t dmac);
    extern int hal_dma_clock_gate_set(uint32_t dmac);

    if (hal_dma_reset_set(DSPI_DMA_CTRL))
        printf("[dspi] dma reset failed\n");

    if (hal_dma_clock_gate_set(DSPI_DMA_CTRL))
        printf("[dspi] dma clock gate failed\n");
#endif
}

/* ==========================================================================
 * SPI 时钟
 * ========================================================================== */

#define DSPI_SYS_CCU_BASE    0x02002000u
#define DSPI_SPI1_CLK_REG    (DSPI_SYS_CCU_BASE + 0x0F08u)

static int dspi_clk_set(uint32_t hz)
{
    uint32_t div, mux, reg;
    int ret;

    if (hz == 0)
        return -1;

    if ((24000000u % hz) == 0) {
        div = 24000000u / hz;
        mux = 0;
    } else if ((200000000u % hz) == 0) {
        div = 200000000u / hz;
        mux = 3;
    } else {
        printf("[dspi] %u Hz 无法整数分频（24M/200M）\n", hz);
        return -1;
    }

    if (div < 1u || div > 32u) {
        printf("[dspi] div %u 超出 1~32\n", div);
        return -1;
    }

    if (mux == 3) {
        hal_clk_t pc;
        ret = hal_n_clk_get_by_clk_num(MAKE_CLKn(AW_SYS_CCU, CLK_PLL_PERI0_200M), &pc);
        if (ret == 0) {
            hal_n_clk_enable(pc);
            hal_n_clk_put(pc);
        }
    }

    reg  = hal_readl(DSPI_SPI1_CLK_REG);
    reg &= ~((0x7u << 24) | 0x1Fu);
    reg |= ((mux & 0x7u) << 24) | ((div - 1u) & 0x1Fu);
    hal_writel(reg, DSPI_SPI1_CLK_REG);

    printf("[dspi] SCLK=%u Hz  MUX=%u  DIV=%u  reg=0x%08x\n",
           hz, mux, div, hal_readl(DSPI_SPI1_CLK_REG));

    return 0;
}

static int dspi_clk_init(void)
{
    hal_rst_t rst;
    hal_clk_t clk_bus, clk;
    int ret;

    rst = NULL; clk_bus = NULL; clk = NULL;

    ret = hal_rst_get_by_rst_num(MAKE_RSTn(AW_SYS_CCU, RST_BUS_SPI1), &rst);
    if (ret) { printf("[dspi] rst get failed %d\n", ret); return -1; }

    ret = hal_n_clk_get_by_clk_num(MAKE_CLKn(AW_SYS_CCU, CLK_BUS_SPI1), &clk_bus);
    if (ret) { printf("[dspi] bus clk get failed %d\n", ret); hal_rst_put(rst); return -1; }

    ret = hal_n_clk_get_by_clk_num(MAKE_CLKn(AW_SYS_CCU, CLK_SPI1), &clk);
    if (ret) {
        printf("[dspi] clk get failed %d\n", ret);
        hal_n_clk_put(clk_bus); hal_rst_put(rst);
        return -1;
    }

    hal_rst_deassert(rst);
    hal_n_clk_enable(clk_bus);
    hal_n_clk_enable(clk);

    hal_n_clk_put(clk);
    hal_n_clk_put(clk_bus);
    hal_rst_put(rst);

    return dspi_clk_set(DSPI_SCLK_HZ);
}

/* ==========================================================================
 * 引脚
 * ========================================================================== */

static void dspi_pin_init(void)
{
    gpio_init_t g;

    memset(&g, 0, sizeof(g));
    g.port      = DSPI_GPIO_PORT;
    g.port_num  = DSPI_GPIO_PINS;
    g.mul_sel   = DSPI_GPIO_FUNC;
    g.pull      = PIN_PULL_DISABLE;
    g.drv_level = PIN_MULTI_DRIVE_2;

    hal_gpio_init(&g);

    printf("[dspi] pins 0x%02x mux=%d\n", (unsigned)DSPI_GPIO_PINS, DSPI_GPIO_FUNC);
}

/* ==========================================================================
 * 中断服务：TC → 换批 / 进入末尾帧保持 / 重装 / 重启
 * ========================================================================== */

static hal_irqreturn_t dspi_isr(void *dev)
{
    uint32_t base  = SPI_BASE(DSPI_PORT);
    uint32_t dbase = DMAC_BASE_ADDR(DSPI_DMA_CTRL);
    uint32_t ch    = DSPI_DMA_CHAN;
    uint32_t en, sta, i;

    en  = hal_readl(base + SUNXI_SPI_INT_CTL_REG) & SUNXI_SPI_INT_CTL_MASK;
    sta = hal_readl(base + SUNXI_SPI_INT_STA_REG);

    hal_writel(sta, base + SUNXI_SPI_INT_STA_REG);      /* 清 pending */

    if (!(sta & en))
        return 0;

    if (sta & (SUNXI_SPI_INT_STA_TX_OVF |
               SUNXI_SPI_INT_STA_RX_OVF |
               SUNXI_SPI_INT_STA_RX_UDR))
        s_err_cnt++;

    if ((sta & SUNXI_SPI_INT_STA_TC) && (en & SUNXI_SPI_INT_CTL_TC_EN)) {

        s_tc_cnt++;

        if (s_pending_ready) {
            /* ---------- 有新数据：切换到新批 ---------- */
            uint32_t nidx = s_active ^ 1u;
            uint32_t nlen = s_pending_len;

            s_desc.src_addr = (uint32_t)(unsigned long)s_buf[nidx];
            s_desc.byte_cnt = nlen;

            s_active        = nidx;
            s_cur_len       = nlen;
            s_pending_ready = false;
            s_hold_mode     = false;        /* 离开保持态 */
            s_switch_cnt++;

        } else if (!s_hold_mode) {
            /* ---------- 无新数据且尚未进入保持态 ----------
             * 把描述符指向当前批的最后一对（X 帧 + Y 帧 = 10 字节），
             * 之后每个 TC 都重复它 → DAC 稳定停在最后一个位置。 */
            uint32_t last = (uint32_t)(unsigned long)s_buf[s_active]
                            + s_cur_len - DSPI_PAIR_BYTES;

            s_desc.src_addr = last;
            s_desc.byte_cnt = DSPI_PAIR_BYTES;

            s_cur_len   = DSPI_PAIR_BYTES;
            s_hold_mode = true;
            s_hold_enter_cnt++;

        } else {
            /* ---------- 已在保持态：描述符不变，继续重复那一对 ---------- */
            s_repeat_cnt++;
        }

        if (s_cur_len == 0)
            return 0;

        /* ---- 清 RX FIFO 残留 ---- */
        if (hal_readl(base + SUNXI_SPI_FIFO_STA_REG) & SUNXI_SPI_FIFO_STA_RX_CNT)
            hal_spi_reset_rxfifo(DSPI_PORT);

        /* ---- 重装 DMA ---- */
        hal_writel(0,    DMA_EN_REG(dbase, ch));
        hal_writel(0x3F, DMA_IRQ_PEND_REG(dbase, ch));
        hal_writel(s_desc_addr, DMA_DESC_ADDR_REG(dbase, ch));
        hal_writel(DMA_CHANNEL_ENABLE, DMA_EN_REG(dbase, ch));

        /* ---- 等 TX FIFO 有数据 ---- */
        for (i = 0; i < 200000u; i++) {
            if (hal_readl(base + SUNXI_SPI_FIFO_STA_REG) & SUNXI_SPI_FIFO_STA_TX_CNT)
                break;
        }
        if (i >= 200000u) {
            s_stall_cnt++;
            return 0;
        }

        /* ---- 按本批长度重设 MBC/MTC，重开 XCH ---- */
        hal_writel(s_cur_len, base + SUNXI_SPI_MBC_REG);
        hal_writel(s_cur_len, base + SUNXI_SPI_MTC_REG);
        hal_writel(hal_readl(base + SUNXI_SPI_TC_REG) | SUNXI_SPI_TC_XCH,
                   base + SUNXI_SPI_TC_REG);
    }

    return 0;
}

/* ==========================================================================
 * DMA 描述符
 * ========================================================================== */

static int dspi_dma_setup(void)
{
    uint32_t dbase = DMAC_BASE_ADDR(DSPI_DMA_CTRL);
    uint32_t ch    = DSPI_DMA_CHAN;
    uint32_t hal_desc_addr;

    hal_writel(0, DMA_EN_REG(dbase, ch));

    s_stream.dmac    = DSPI_DMA_CTRL;
    s_stream.channel = DSPI_DMA_CHAN;
    hal_dma_deinit(&s_stream);

    memset(&s_dma_cfg, 0, sizeof(s_dma_cfg));

    s_dma_cfg.dst_data_width = DMA_DEST_DATA_WIDTH_8BIT;
    s_dma_cfg.dst_addr_mode  = DMA_DEST_ADDR_MODE_IO;
    s_dma_cfg.dst_block_size = DMA_DEST_BLOCK_SIZE_1BYTE;
    s_dma_cfg.dst_drq_type   = DSPI_DRQ_TX;

    s_dma_cfg.src_data_width = DMA_SRC_DATA_WIDTH_8BIT;
    s_dma_cfg.src_addr_mode  = DMA_SRC_ADDR_MODE_LINEAR;
    s_dma_cfg.src_block_size = DMA_SRC_BLOCK_SIZE_1BYTE;
    s_dma_cfg.src_drq_type   = DRQSRC_SDRAM;

    s_dma_cfg.desc_src_addr  = (uint32_t)(unsigned long)s_buf[0];
    s_dma_cfg.desc_dst_addr  = (uint32_t)(SPI_BASE(DSPI_PORT) + SUNXI_SPI_TXDATA_REG);
    s_dma_cfg.desc_byte_cnt  = DSPI_INIT_PAIRS * DSPI_PAIR_BYTES;
    s_dma_cfg.is_timeout     = false;
    s_dma_cfg.loop_mode      = false;

    /* hal_dma_init 负责：通道 non-secure、AUTO_GATE、DRQ 路由、生成描述符 */
    if (hal_dma_init(&s_stream, &s_dma_cfg)) {
        printf("[dspi] dma init failed\n");
        return -1;
    }

    /* 把 HAL 生成的描述符当模板复制到自己的 nocache 描述符 */
    hal_desc_addr = hal_readl(DMA_DESC_ADDR_REG(dbase, ch));
    memcpy(&s_desc, (const void *)(unsigned long)hal_desc_addr, sizeof(s_desc));

    s_desc.src_addr  = (uint32_t)(unsigned long)s_buf[0];
    s_desc.byte_cnt  = DSPI_INIT_PAIRS * DSPI_PAIR_BYTES;
    s_desc.parameter = 0;
    s_desc.link      = 0xFFFFF800u;         /* LINK_END：单描述符 */

    s_desc_addr = (uint32_t)(unsigned long)&s_desc;

    printf("[dspi] dma ok  hal_desc=0x%08x  our_desc=0x%08x  cfg=0x%08x\n",
           hal_desc_addr, s_desc_addr, s_desc.cfg);

    return 0;
}

/* ==========================================================================
 * 对外接口：提交一批可变长度数据
 * ========================================================================== */

/*
 * 提交一批数据。
 *   x, y : 各 n 个点（0~4095）
 *   n    : 点数，1 ~ DSPI_PAIRS
 *
 * 返回： 0 成功排队 / -1 参数错 / -2 上一批未消费
 *
 * 若当前处于「末尾帧保持」状态，submit 成功后会立即离开保持态。
 */
int ms5612m_submit(const uint16_t *x, const uint16_t *y, uint32_t n)
{
    uint32_t idx, len;

    if (!x || !y || n == 0 || n > DSPI_PAIRS)
        return -1;

    if (s_pending_ready) {
        s_busy_cnt++;
        return -2;
    }

    idx = s_active ^ 1u;
    len = dspi_encode_pairs(s_buf[idx], x, y, n);

    // hal_dma_flush_dcache_to_mem((unsigned long)s_buf[idx], len);

    s_pending_len   = len;
    __sync_synchronize();
    s_pending_ready = true;

    return 0;
}

/* 便捷接口：提交 1 个点（发完即进入末尾帧保持） */
int ms5612m_submit_one(uint16_t x, uint16_t y)
{
    return ms5612m_submit(&x, &y, 1);
}

/* 查询是否处于末尾帧保持状态 */
bool ms5612m_is_holding(void)
{
    return s_hold_mode;
}

/* ==========================================================================
 * 初始化 / 启动
 * ========================================================================== */

void ms5612m_dspi_init(void)
{
    spi_init_t cfg;
    hal_irq_init_t irq;
    int ret;
    uint32_t i;

    s_tc_cnt         = 0;
    s_switch_cnt     = 0;
    s_hold_enter_cnt = 0;
    s_repeat_cnt     = 0;
    s_busy_cnt       = 0;
    s_stall_cnt      = 0;
    s_err_cnt        = 0;
    s_active         = 0;
    s_pending_ready  = false;
    s_hold_mode      = false;
    s_pending_len    = 0;
    s_cur_len        = 0;

    printf("\n[ms5612m] ==== dspi v3 init ====\n");

    hal_spi_deinit(DSPI_PORT);

    dspi_dma_clk_init();
    dspi_clk_init();
    dspi_hw_reset();
    dspi_pin_init();

    memset(&cfg, 0, sizeof(cfg));
    cfg.bus_mode        = HAL_SPI_BUS_MASTER;
    cfg.cs_mode         = HAL_SPI_CS_AUTO;
    cfg.chipselect      = 0;
    cfg.mode            = SPI_MODE_2;
    cfg.sip             = 0;
    cfg.flash           = 0;
    cfg.use_dma         = false;
    cfg.clock_frequency = DSPI_SCLK_HZ;

    ret = hal_spi_init(DSPI_PORT, &cfg);
    if (ret < 0) {
        printf("[dspi] hal_spi_init failed %d\n", ret);
        return;
    }

    memset(&irq, 0, sizeof(irq));
    irq.irqn               = DSPI_SPI_IRQ;
    irq.preemptionpriority = HAL_IRQ_PRIO_TOP;
    irq.subpriority        = HAL_IRQ_SUBPRIO_TOP;
    irq.cmd                = HAL_INIT_CMD_ENABLE;
    irq.isr_info.func      = dspi_isr;
    irq.isr_info.parg      = NULL;
    hal_v2_intc_irq_config(&irq);

    hal_spi_disable_irq(DSPI_PORT, SUNXI_SPI_INT_CTL_MASK);
    hal_spi_clr_irq_pending(DSPI_PORT, SUNXI_SPI_INT_STA_MASK);
    hal_spi_enable_irq(DSPI_PORT,
                       SUNXI_SPI_INT_CTL_TC_EN |
                       SUNXI_SPI_INT_CTL_TX_OVF_EN |
                       SUNXI_SPI_INT_CTL_RX_OVF_EN |
                       SUNXI_SPI_INT_CTL_RX_UDR_EN);

    /* 初始批次：DSPI_INIT_PAIRS 个相同的保持点 */
    for (i = 0; i < DSPI_INIT_PAIRS; i++) {
        s_dx[i] = 0;
        s_dy[i] = 4095;
    }
    s_cur_len = dspi_encode_pairs(s_buf[0], s_dx, s_dy, DSPI_INIT_PAIRS);
    hal_dma_flush_dcache_to_mem((unsigned long)s_buf[0], s_cur_len);

    if (dspi_dma_setup())
        return;

    printf("[ms5612m] init done, init batch = %u bytes (%u points)\n",
           s_cur_len, DSPI_INIT_PAIRS);
}

void ms5612m_stream_start(void)
{
    uint32_t base = SPI_BASE(DSPI_PORT);
    uint32_t tc, bcc, i;

    printf("[ms5612m] stream start\n");

    /* TC：DHB / CPOL / CPHA / SSCTL（绕开 hal_spi_xfer 必须自己写） */
    tc  = hal_readl(base + SUNXI_SPI_TC_REG);
    tc |=  SUNXI_SPI_TC_DHB;                 /* ★ 丢弃接收数据，否则 RX FIFO 灌满卡死 */
    tc |=  SUNXI_SPI_TC_CPOL;                /* MODE_2：idle 高 */
    tc &= ~SUNXI_SPI_TC_CPHA;
    tc &= ~SUNXI_SPI_TC_SSCTL;
    hal_writel(tc, base + SUNXI_SPI_TC_REG);

    /* BCC：双线 + STC=0 */
    bcc  = hal_readl(base + SUNXI_SPI_BCC_REG);
    bcc |=  SUNXI_SPI_BCC_DRM;
    bcc &= ~SUNXI_SPI_BCC_QUAD_EN;
    bcc &= ~SUNXI_SPI_BCC_STC;
    hal_writel(bcc, base + SUNXI_SPI_BCC_REG);

    hal_spi_enable_dma_irq(DSPI_PORT, SUNXI_SPI_FIFO_CTL_TX_DRQ_EN);

    hal_writel(s_cur_len, base + SUNXI_SPI_MBC_REG);
    hal_writel(s_cur_len, base + SUNXI_SPI_MTC_REG);

    hal_writel(s_desc_addr,
               DMA_DESC_ADDR_REG(DMAC_BASE_ADDR(DSPI_DMA_CTRL), DSPI_DMA_CHAN));
    hal_writel(DMA_CHANNEL_ENABLE,
               DMA_EN_REG(DMAC_BASE_ADDR(DSPI_DMA_CTRL), DSPI_DMA_CHAN));

    for (i = 0; i < 100000u; i++) {
        if (hal_readl(base + SUNXI_SPI_FIFO_STA_REG) & SUNXI_SPI_FIFO_STA_TX_CNT)
            break;
    }
    if (i >= 100000u)
        printf("[ms5612m] warn: fifo empty before XCH\n");

    hal_writel(hal_readl(base + SUNXI_SPI_TC_REG) | SUNXI_SPI_TC_XCH,
               base + SUNXI_SPI_TC_REG);

    printf("[ms5612m] running\n");
}

/* ==========================================================================
 * 状态打印
 * ========================================================================== */

void ms5612m_dspi_stat(void)
{
    uint32_t dbase = DMAC_BASE_ADDR(DSPI_DMA_CTRL);
    uint32_t ch    = DSPI_DMA_CHAN;

    printf("[stat] TC=%u sw=%u hold_in=%u rep=%u busy=%u stall=%u err=%u | "
           "curlen=%u pend=%u HOLD=%u | EN=%u BCNT=%u\n",
           (unsigned)s_tc_cnt, (unsigned)s_switch_cnt, (unsigned)s_hold_enter_cnt,
           (unsigned)s_repeat_cnt, (unsigned)s_busy_cnt, (unsigned)s_stall_cnt,
           (unsigned)s_err_cnt,
           (unsigned)s_cur_len, (unsigned)(s_pending_ready ? s_pending_len : 0),
           (unsigned)(s_hold_mode ? 1u : 0u),
           (unsigned)hal_readl(DMA_EN_REG(dbase, ch)),
           (unsigned)hal_readl(DMA_BCNT_LEFT_REG(dbase, ch)));
}

/* ==========================================================================
 * 演示波形
 * ========================================================================== */
#include <math.h>
#if DSPI_DEMO_MODE == DSPI_DEMO_TRIANGLE
/* 三角波：0 → 4095 → 0，无瞬跳（period 必须是偶数） */
static uint16_t demo_tri(uint32_t t, uint32_t period)
{
    uint32_t p    = t % period;
    uint32_t half = period / 2u;

    if (p < half)
        return (uint16_t)((p * 4095u) / half);
    else
        return (uint16_t)(((period - p) * 4095u) / half);
}
#endif

/* 生成第 t 个点（t 是跨批次连续的全局序号） */
static void demo_point(uint32_t t, uint16_t *x, uint16_t *y)
{
#if DSPI_DEMO_MODE == DSPI_DEMO_TRIANGLE
    *x = demo_tri(t, 4000u);        /* X 周期 4000 点 */
    *y = demo_tri(t, 7000u);        /* Y 周期 7000 点 → 李萨如 */
#elif DSPI_DEMO_MODE == DSPI_DEMO_SIN_COS
    float T = 2*3.14f;
    int steps_per_T = 128;
    *x = (sinf((float)t/steps_per_T * T)+1.0)/2.0 * 4095;        /* X 周期 4000 点 */
    *y = (sinf((float)t/steps_per_T * T+ 0.25*T)+1.0)/2.0 * 4095;        /* Y 周期 7000 点 → 李萨如 */
#else
    *x = (uint16_t)((t * 7u) & 0x0FFFu);
    *y = (uint16_t)((t * 3u) & 0x0FFFu);
#endif
}

/* ==========================================================================
 * 演示线程
 * ========================================================================== */

static const uint32_t s_demo_n[] = {
    1u, 2u, 8u, 50u, 400u, DSPI_PAIRS, 1u, 100u
};

void ms5612m_dspi_dma_by_ds_thread(void *param)
{
    uint32_t k, n, i, phase;

    (void)param;

    printf("\n[ms5612m] thread start\n");

    ms5612m_dspi_init();
    ms5612m_stream_start();
    
    phase = 0;

    
    for (;;) {
        for (k = 5; k < (sizeof(s_demo_n) / sizeof(s_demo_n[0])); k++) {

            n = s_demo_n[k];

            for (i = 0; i < n; i++)
                demo_point(phase + i, &s_dx[i], &s_dy[i]);

            while (ms5612m_submit(s_dx, s_dy, n) == -2)
                vTaskDelay(1);

            // printf("[demo] submit n=%u (%u bytes)\n", n, n * DSPI_PAIR_BYTES);

            phase += n;

            // vTaskDelay(10);
            break;
        }

        /* 故意停 2 秒不提交，用来观察"末尾帧保持"是否生效：
         * 这段时间内 HOLD 应该变 1，rep 持续增长，DAC 停在最后位置。 */
        // printf("[demo] pause 2s -> expect HOLD=1\n");
        // vTaskDelay(20);

#if DSPI_ENABLE_STAT
        // ms5612m_dspi_stat();
#endif
    }
}
