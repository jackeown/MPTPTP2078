%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LCNM8zD2vY

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:57 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  419 (2319 expanded)
%              Number of leaves         :   41 ( 624 expanded)
%              Depth                    :   83
%              Number of atoms          : 8535 (47672 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_yellow_6_type,type,(
    k6_yellow_6: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t37_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_compts_1 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ? [C: $i] :
                ( ( v3_yellow_6 @ C @ A )
                & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( v1_compts_1 @ A )
        <=> ! [B: $i] :
              ( ( ~ ( v2_struct_0 @ B )
                & ( v4_orders_2 @ B )
                & ( v7_waybel_0 @ B )
                & ( l1_waybel_0 @ B @ A ) )
             => ? [C: $i] :
                  ( ( v3_yellow_6 @ C @ A )
                  & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_yellow19])).

thf('0',plain,(
    ! [X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v4_orders_2 @ X37 )
      | ~ ( v7_waybel_0 @ X37 )
      | ~ ( l1_waybel_0 @ X37 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X36: $i] :
      ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
      | ~ ( v3_yellow_6 @ X36 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X36: $i] :
        ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( v4_orders_2 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v4_orders_2 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('13',plain,(
    ! [X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v4_orders_2 @ X37 )
      | ~ ( v7_waybel_0 @ X37 )
      | ~ ( l1_waybel_0 @ X37 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(l37_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_compts_1 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ? [C: $i] :
                ( ( r3_waybel_9 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_compts_1 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X31 )
      | ( r3_waybel_9 @ X31 @ X32 @ ( sk_C_1 @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('18',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('28',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('30',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_compts_1 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ X31 )
      | ( m1_subset_1 @ ( sk_C_1 @ X32 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(t32_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r3_waybel_9 @ A @ B @ C )
                  & ! [D: $i] :
                      ( ( m2_yellow_6 @ D @ A @ B )
                     => ~ ( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ( m2_yellow_6 @ ( sk_D @ X30 @ X28 @ X29 ) @ X29 @ X28 )
      | ~ ( r3_waybel_9 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
        | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) @ sk_A @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
        | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) @ sk_A @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','45'])).

thf('47',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('48',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('49',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(dt_m2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m2_yellow_6 @ C @ A @ B )
         => ( ~ ( v2_struct_0 @ C )
            & ( v4_orders_2 @ C )
            & ( v7_waybel_0 @ C )
            & ( l1_waybel_0 @ C @ A ) ) ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( v4_orders_2 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('57',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('58',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('60',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('67',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( v7_waybel_0 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('70',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('71',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('78',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( l1_waybel_0 @ X18 @ X16 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('81',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('82',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf(d19_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( v3_yellow_6 @ B @ A )
          <=> ( ( k10_yellow_6 @ A @ B )
             != k1_xboole_0 ) ) ) ) )).

thf('88',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ( ( k10_yellow_6 @ X20 @ X19 )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_yellow_6])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','94'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('98',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('99',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v4_orders_2 @ X28 )
      | ~ ( v7_waybel_0 @ X28 )
      | ~ ( l1_waybel_0 @ X28 @ X29 )
      | ( r2_hidden @ X30 @ ( k10_yellow_6 @ X29 @ ( sk_D @ X30 @ X28 @ X29 ) ) )
      | ~ ( r3_waybel_9 @ X29 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
        | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_1 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
        | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('106',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('107',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('112',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['96','113'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('115',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('119',plain,
    ( ! [X36: $i] :
        ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
   <= ! [X36: $i] :
        ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X36 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('126',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ~ ( v2_struct_0 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('129',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('130',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B_1 )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['124','135'])).

thf('137',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
   <= ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('138',plain,
    ( ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf(t36_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_compts_1 @ A )
      <=> ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ~ ( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) )
                & ! [C: $i] :
                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                   => ~ ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) )).

thf('140',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('141',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('142',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('143',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('144',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('145',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('146',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('147',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('148',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['145','157'])).

thf('159',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( v7_waybel_0 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['144','167'])).

thf('169',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['143','172'])).

thf('174',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['142','177'])).

thf('179',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('184',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('185',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('186',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('187',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( v4_orders_2 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('188',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('190',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['185','191'])).

thf('193',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['184','196'])).

thf('198',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['183','201'])).

thf('203',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('208',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('209',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('210',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['208','214'])).

thf('216',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['207','219'])).

thf('221',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('226',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('227',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('228',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('229',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( l1_waybel_0 @ X18 @ X16 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('230',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('232',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['227','233'])).

thf('235',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['226','238'])).

thf('240',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['225','243'])).

thf('245',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('250',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('251',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('252',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('253',plain,
    ( ( ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('254',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('255',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('256',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('257',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('258',plain,
    ( ( ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('259',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf(dt_k10_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('260',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v7_waybel_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('261',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['261','262','263'])).

thf('265',plain,
    ( ( ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['258','265'])).

thf('267',plain,
    ( ( ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['257','267'])).

thf('269',plain,
    ( ( ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('270',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('271',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['256','271'])).

thf('273',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t29_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) )
               => ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) )).

thf('274',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( k10_yellow_6 @ X22 @ X21 ) )
      | ( r3_waybel_9 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_waybel_9])).

thf('275',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_yellow_6 @ X1 @ X0 ) @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ ( sk_C @ X2 @ ( k10_yellow_6 @ X1 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r3_waybel_9 @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_yellow_6 @ X1 @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['272','275'])).

thf('277',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['255','280'])).

thf('282',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['254','282'])).

thf('284',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['253','284'])).

thf('286',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['256','271'])).

thf(t31_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m2_yellow_6 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r3_waybel_9 @ A @ C @ D )
                   => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) )).

thf('288',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v7_waybel_0 @ X24 )
      | ~ ( l1_waybel_0 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( r3_waybel_9 @ X25 @ X24 @ X26 )
      | ~ ( r3_waybel_9 @ X25 @ X27 @ X26 )
      | ~ ( m2_yellow_6 @ X27 @ X25 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_waybel_9])).

thf('289',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m2_yellow_6 @ X2 @ sk_A @ X1 )
        | ~ ( r3_waybel_9 @ sk_A @ X2 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ( v2_struct_0 @ X1 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['287','288'])).

thf('290',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m2_yellow_6 @ X2 @ sk_A @ X1 )
        | ~ ( r3_waybel_9 @ sk_A @ X2 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ( v2_struct_0 @ X1 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['289','290','291'])).

thf('293',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( r3_waybel_9 @ sk_A @ X2 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( m2_yellow_6 @ X2 @ sk_A @ X1 )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ~ ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ X1 )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ( v2_struct_0 @ X1 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['286','293'])).

thf('295',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ X1 )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['252','295'])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['251','297'])).

thf('299',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['250','302'])).

thf('304',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['303','304','305'])).

thf('307',plain,
    ( ! [X0: $i] :
        ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['306'])).

thf('308',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['249','307'])).

thf('309',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['308','309','310'])).

thf('312',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['256','271'])).

thf('314',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r3_waybel_9 @ X33 @ ( sk_B @ X33 ) @ X34 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('315',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['315','316','317'])).

thf('319',plain,
    ( ! [X0: $i] :
        ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['312','319'])).

thf('321',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('323',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('324',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['322','323'])).

thf('325',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['321','324'])).

thf('326',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X20 )
      | ~ ( v3_yellow_6 @ X19 @ X20 )
      | ( ( k10_yellow_6 @ X20 @ X19 )
       != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_yellow_6])).

thf('327',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['327','328','329'])).

thf('331',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['248','331'])).

thf('333',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v3_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['224','333'])).

thf('335',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['206','335'])).

thf('337',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['182','337'])).

thf('339',plain,
    ( ( ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['338'])).

thf('340',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('341',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('342',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ~ ( v2_struct_0 @ X18 )
      | ~ ( m2_yellow_6 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('343',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['343','344'])).

thf('346',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['345'])).

thf('347',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['340','346'])).

thf('348',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['347','348','349'])).

thf('351',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_3 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['350'])).

thf('352',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['339','351'])).

thf('353',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['141','353'])).

thf('355',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('357',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['354','355','356'])).

thf('358',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['140','358'])).

thf('360',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['359','360','361'])).

thf('363',plain,
    ( ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['362'])).

thf('364',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(clc,[status(thm)],['363','364'])).

thf('366',plain,(
    ! [X33: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('367',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['365','366'])).

thf('368',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['367','368','369'])).

thf('371',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('373',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(clc,[status(thm)],['371','372'])).

thf('374',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('375',plain,
    ( ~ ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ~ ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_3 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['373','374'])).

thf('376',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','138','139','375'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LCNM8zD2vY
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.91/2.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.91/2.10  % Solved by: fo/fo7.sh
% 1.91/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.10  % done 1771 iterations in 1.630s
% 1.91/2.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.91/2.10  % SZS output start Refutation
% 1.91/2.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.91/2.10  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.91/2.10  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 1.91/2.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.91/2.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.91/2.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.91/2.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.91/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.10  thf(k6_yellow_6_type, type, k6_yellow_6: $i > $i).
% 1.91/2.10  thf(sk_B_type, type, sk_B: $i > $i).
% 1.91/2.10  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 1.91/2.10  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.91/2.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.91/2.10  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 1.91/2.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.91/2.10  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 1.91/2.10  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.91/2.10  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 1.91/2.10  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 1.91/2.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.91/2.10  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 1.91/2.10  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.91/2.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.91/2.10  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 1.91/2.10  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.91/2.10  thf(t37_yellow19, conjecture,
% 1.91/2.10    (![A:$i]:
% 1.91/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.10       ( ( v1_compts_1 @ A ) <=>
% 1.91/2.10         ( ![B:$i]:
% 1.91/2.10           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.10               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.10             ( ?[C:$i]:
% 1.91/2.10               ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ))).
% 1.91/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.10    (~( ![A:$i]:
% 1.91/2.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.91/2.10            ( l1_pre_topc @ A ) ) =>
% 1.91/2.10          ( ( v1_compts_1 @ A ) <=>
% 1.91/2.10            ( ![B:$i]:
% 1.91/2.10              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.10                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.10                ( ?[C:$i]:
% 1.91/2.10                  ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ) )),
% 1.91/2.10    inference('cnf.neg', [status(esa)], [t37_yellow19])).
% 1.91/2.10  thf('0', plain,
% 1.91/2.10      (![X37 : $i]:
% 1.91/2.10         ((v2_struct_0 @ X37)
% 1.91/2.10          | ~ (v4_orders_2 @ X37)
% 1.91/2.10          | ~ (v7_waybel_0 @ X37)
% 1.91/2.10          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.10          | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37)
% 1.91/2.10          | (v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('1', plain,
% 1.91/2.10      ((![X37 : $i]:
% 1.91/2.10          ((v2_struct_0 @ X37)
% 1.91/2.10           | ~ (v4_orders_2 @ X37)
% 1.91/2.10           | ~ (v7_waybel_0 @ X37)
% 1.91/2.10           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.10           | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))) | 
% 1.91/2.10       ((v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('split', [status(esa)], ['0'])).
% 1.91/2.10  thf('2', plain,
% 1.91/2.10      (![X36 : $i]:
% 1.91/2.10         (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 1.91/2.10          | ~ (v3_yellow_6 @ X36 @ sk_A)
% 1.91/2.10          | ~ (v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('3', plain,
% 1.91/2.10      ((![X36 : $i]:
% 1.91/2.10          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 1.91/2.10       ~ ((v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('split', [status(esa)], ['2'])).
% 1.91/2.10  thf('4', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('5', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('6', plain, (((v7_waybel_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('7', plain, (((v7_waybel_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('8', plain, (((v4_orders_2 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('9', plain, (((v4_orders_2 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('10', plain, ((~ (v2_struct_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('11', plain, (~ ((v2_struct_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('split', [status(esa)], ['10'])).
% 1.91/2.10  thf('12', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('13', plain,
% 1.91/2.10      (![X37 : $i]:
% 1.91/2.10         ((v2_struct_0 @ X37)
% 1.91/2.10          | ~ (v4_orders_2 @ X37)
% 1.91/2.10          | ~ (v7_waybel_0 @ X37)
% 1.91/2.10          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.10          | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A)
% 1.91/2.10          | (v1_compts_1 @ sk_A))),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('14', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['13'])).
% 1.91/2.10  thf('15', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('16', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf(l37_yellow19, axiom,
% 1.91/2.10    (![A:$i]:
% 1.91/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.10       ( ( v1_compts_1 @ A ) =>
% 1.91/2.10         ( ![B:$i]:
% 1.91/2.10           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.10               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.10             ( ?[C:$i]:
% 1.91/2.10               ( ( r3_waybel_9 @ A @ B @ C ) & 
% 1.91/2.10                 ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 1.91/2.10  thf('17', plain,
% 1.91/2.10      (![X31 : $i, X32 : $i]:
% 1.91/2.10         (~ (v1_compts_1 @ X31)
% 1.91/2.10          | (v2_struct_0 @ X32)
% 1.91/2.10          | ~ (v4_orders_2 @ X32)
% 1.91/2.10          | ~ (v7_waybel_0 @ X32)
% 1.91/2.10          | ~ (l1_waybel_0 @ X32 @ X31)
% 1.91/2.10          | (r3_waybel_9 @ X31 @ X32 @ (sk_C_1 @ X32 @ X31))
% 1.91/2.10          | ~ (l1_pre_topc @ X31)
% 1.91/2.10          | ~ (v2_pre_topc @ X31)
% 1.91/2.10          | (v2_struct_0 @ X31))),
% 1.91/2.10      inference('cnf', [status(esa)], [l37_yellow19])).
% 1.91/2.10  thf('18', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.10         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.10         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['16', '17'])).
% 1.91/2.10  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('21', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.91/2.10  thf('22', plain,
% 1.91/2.10      (((~ (v1_compts_1 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['15', '21'])).
% 1.91/2.10  thf('23', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['14', '22'])).
% 1.91/2.10  thf('24', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['12', '23'])).
% 1.91/2.10  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('26', plain,
% 1.91/2.10      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['24', '25'])).
% 1.91/2.10  thf('27', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('28', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['13'])).
% 1.91/2.10  thf('29', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('30', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('31', plain,
% 1.91/2.10      (![X31 : $i, X32 : $i]:
% 1.91/2.10         (~ (v1_compts_1 @ X31)
% 1.91/2.10          | (v2_struct_0 @ X32)
% 1.91/2.10          | ~ (v4_orders_2 @ X32)
% 1.91/2.10          | ~ (v7_waybel_0 @ X32)
% 1.91/2.10          | ~ (l1_waybel_0 @ X32 @ X31)
% 1.91/2.10          | (m1_subset_1 @ (sk_C_1 @ X32 @ X31) @ (u1_struct_0 @ X31))
% 1.91/2.10          | ~ (l1_pre_topc @ X31)
% 1.91/2.10          | ~ (v2_pre_topc @ X31)
% 1.91/2.10          | (v2_struct_0 @ X31))),
% 1.91/2.10      inference('cnf', [status(esa)], [l37_yellow19])).
% 1.91/2.10  thf('32', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.10         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.10         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['30', '31'])).
% 1.91/2.10  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('35', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.91/2.10  thf('36', plain,
% 1.91/2.10      (((~ (v1_compts_1 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['29', '35'])).
% 1.91/2.10  thf('37', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['28', '36'])).
% 1.91/2.10  thf('38', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['27', '37'])).
% 1.91/2.10  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('40', plain,
% 1.91/2.10      ((((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['38', '39'])).
% 1.91/2.10  thf(t32_waybel_9, axiom,
% 1.91/2.10    (![A:$i]:
% 1.91/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.10       ( ![B:$i]:
% 1.91/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.10             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.10           ( ![C:$i]:
% 1.91/2.10             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.91/2.10               ( ~( ( r3_waybel_9 @ A @ B @ C ) & 
% 1.91/2.10                    ( ![D:$i]:
% 1.91/2.10                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 1.91/2.10                        ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.10  thf('41', plain,
% 1.91/2.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.91/2.10         ((v2_struct_0 @ X28)
% 1.91/2.10          | ~ (v4_orders_2 @ X28)
% 1.91/2.10          | ~ (v7_waybel_0 @ X28)
% 1.91/2.10          | ~ (l1_waybel_0 @ X28 @ X29)
% 1.91/2.10          | (m2_yellow_6 @ (sk_D @ X30 @ X28 @ X29) @ X29 @ X28)
% 1.91/2.10          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 1.91/2.10          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 1.91/2.10          | ~ (l1_pre_topc @ X29)
% 1.91/2.10          | ~ (v2_pre_topc @ X29)
% 1.91/2.10          | (v2_struct_0 @ X29))),
% 1.91/2.10      inference('cnf', [status(esa)], [t32_waybel_9])).
% 1.91/2.10  thf('42', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          ((v2_struct_0 @ sk_B_1)
% 1.91/2.10           | (v2_struct_0 @ sk_A)
% 1.91/2.10           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.10           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.10           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10           | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 1.91/2.10              sk_A @ X0)
% 1.91/2.10           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.91/2.10           | ~ (v7_waybel_0 @ X0)
% 1.91/2.10           | ~ (v4_orders_2 @ X0)
% 1.91/2.10           | (v2_struct_0 @ X0)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['40', '41'])).
% 1.91/2.10  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('45', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          ((v2_struct_0 @ sk_B_1)
% 1.91/2.10           | (v2_struct_0 @ sk_A)
% 1.91/2.10           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10           | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 1.91/2.10              sk_A @ X0)
% 1.91/2.10           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.91/2.10           | ~ (v7_waybel_0 @ X0)
% 1.91/2.10           | ~ (v4_orders_2 @ X0)
% 1.91/2.10           | (v2_struct_0 @ X0)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.91/2.10  thf('46', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['26', '45'])).
% 1.91/2.10  thf('47', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('48', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('49', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('50', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 1.91/2.10  thf('51', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['50'])).
% 1.91/2.10  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('53', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['51', '52'])).
% 1.91/2.10  thf(dt_m2_yellow_6, axiom,
% 1.91/2.10    (![A:$i,B:$i]:
% 1.91/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 1.91/2.10         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.10         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.10       ( ![C:$i]:
% 1.91/2.10         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 1.91/2.10           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 1.91/2.10             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 1.91/2.10  thf('54', plain,
% 1.91/2.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.10         (~ (l1_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X17)
% 1.91/2.10          | ~ (v4_orders_2 @ X17)
% 1.91/2.10          | ~ (v7_waybel_0 @ X17)
% 1.91/2.10          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.10          | (v4_orders_2 @ X18)
% 1.91/2.10          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.10      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.10  thf('55', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['53', '54'])).
% 1.91/2.10  thf('56', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('57', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('58', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf(dt_l1_pre_topc, axiom,
% 1.91/2.10    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.91/2.10  thf('60', plain,
% 1.91/2.10      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 1.91/2.10      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.91/2.10  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.10      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.10  thf('62', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['55', '56', '57', '58', '61'])).
% 1.91/2.10  thf('63', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['62'])).
% 1.91/2.10  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('65', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['63', '64'])).
% 1.91/2.10  thf('66', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['51', '52'])).
% 1.91/2.10  thf('67', plain,
% 1.91/2.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.10         (~ (l1_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X17)
% 1.91/2.10          | ~ (v4_orders_2 @ X17)
% 1.91/2.10          | ~ (v7_waybel_0 @ X17)
% 1.91/2.10          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.10          | (v7_waybel_0 @ X18)
% 1.91/2.10          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.10      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.10  thf('68', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['66', '67'])).
% 1.91/2.10  thf('69', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('70', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('71', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.10      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.10  thf('73', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 1.91/2.10  thf('74', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['73'])).
% 1.91/2.10  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('76', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['74', '75'])).
% 1.91/2.10  thf('77', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['51', '52'])).
% 1.91/2.10  thf('78', plain,
% 1.91/2.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.10         (~ (l1_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X17)
% 1.91/2.10          | ~ (v4_orders_2 @ X17)
% 1.91/2.10          | ~ (v7_waybel_0 @ X17)
% 1.91/2.10          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.10          | (l1_waybel_0 @ X18 @ X16)
% 1.91/2.10          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.10      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.10  thf('79', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['77', '78'])).
% 1.91/2.10  thf('80', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('81', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('82', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.10      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.10  thf('84', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 1.91/2.10  thf('85', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['84'])).
% 1.91/2.10  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('87', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['85', '86'])).
% 1.91/2.10  thf(d19_yellow_6, axiom,
% 1.91/2.10    (![A:$i]:
% 1.91/2.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.10       ( ![B:$i]:
% 1.91/2.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.10             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.10           ( ( v3_yellow_6 @ B @ A ) <=>
% 1.91/2.10             ( ( k10_yellow_6 @ A @ B ) != ( k1_xboole_0 ) ) ) ) ) ))).
% 1.91/2.10  thf('88', plain,
% 1.91/2.10      (![X19 : $i, X20 : $i]:
% 1.91/2.10         ((v2_struct_0 @ X19)
% 1.91/2.10          | ~ (v4_orders_2 @ X19)
% 1.91/2.10          | ~ (v7_waybel_0 @ X19)
% 1.91/2.10          | ~ (l1_waybel_0 @ X19 @ X20)
% 1.91/2.10          | ((k10_yellow_6 @ X20 @ X19) = (k1_xboole_0))
% 1.91/2.10          | (v3_yellow_6 @ X19 @ X20)
% 1.91/2.10          | ~ (l1_pre_topc @ X20)
% 1.91/2.10          | ~ (v2_pre_topc @ X20)
% 1.91/2.10          | (v2_struct_0 @ X20))),
% 1.91/2.10      inference('cnf', [status(esa)], [d19_yellow_6])).
% 1.91/2.10  thf('89', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.10         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | ((k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 1.91/2.10         | ~ (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['87', '88'])).
% 1.91/2.10  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('92', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | ((k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 1.91/2.10         | ~ (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.91/2.10  thf('93', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ((k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['76', '92'])).
% 1.91/2.10  thf('94', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | ((k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 1.91/2.10         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['93'])).
% 1.91/2.10  thf('95', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ((k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['65', '94'])).
% 1.91/2.10  thf('96', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | ((k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['95'])).
% 1.91/2.10  thf('97', plain,
% 1.91/2.10      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['24', '25'])).
% 1.91/2.10  thf('98', plain,
% 1.91/2.10      ((((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['38', '39'])).
% 1.91/2.10  thf('99', plain,
% 1.91/2.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.91/2.10         ((v2_struct_0 @ X28)
% 1.91/2.10          | ~ (v4_orders_2 @ X28)
% 1.91/2.10          | ~ (v7_waybel_0 @ X28)
% 1.91/2.10          | ~ (l1_waybel_0 @ X28 @ X29)
% 1.91/2.10          | (r2_hidden @ X30 @ (k10_yellow_6 @ X29 @ (sk_D @ X30 @ X28 @ X29)))
% 1.91/2.10          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 1.91/2.10          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 1.91/2.10          | ~ (l1_pre_topc @ X29)
% 1.91/2.10          | ~ (v2_pre_topc @ X29)
% 1.91/2.10          | (v2_struct_0 @ X29))),
% 1.91/2.10      inference('cnf', [status(esa)], [t32_waybel_9])).
% 1.91/2.10  thf('100', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          ((v2_struct_0 @ sk_B_1)
% 1.91/2.10           | (v2_struct_0 @ sk_A)
% 1.91/2.10           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.10           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.10           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10           | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 1.91/2.10              (k10_yellow_6 @ sk_A @ 
% 1.91/2.10               (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 1.91/2.10           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.91/2.10           | ~ (v7_waybel_0 @ X0)
% 1.91/2.10           | ~ (v4_orders_2 @ X0)
% 1.91/2.10           | (v2_struct_0 @ X0)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['98', '99'])).
% 1.91/2.10  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('103', plain,
% 1.91/2.10      ((![X0 : $i]:
% 1.91/2.10          ((v2_struct_0 @ sk_B_1)
% 1.91/2.10           | (v2_struct_0 @ sk_A)
% 1.91/2.10           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10           | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 1.91/2.10              (k10_yellow_6 @ sk_A @ 
% 1.91/2.10               (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 1.91/2.10           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 1.91/2.10           | ~ (v7_waybel_0 @ X0)
% 1.91/2.10           | ~ (v4_orders_2 @ X0)
% 1.91/2.10           | (v2_struct_0 @ X0)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.91/2.10  thf('104', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.91/2.10         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            (k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['97', '103'])).
% 1.91/2.10  thf('105', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('106', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('107', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('108', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            (k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.91/2.10  thf('109', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            (k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['108'])).
% 1.91/2.10  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('111', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            (k10_yellow_6 @ sk_A @ 
% 1.91/2.10             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['109', '110'])).
% 1.91/2.10  thf(t7_ordinal1, axiom,
% 1.91/2.10    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.10  thf('112', plain,
% 1.91/2.10      (![X11 : $i, X12 : $i]:
% 1.91/2.10         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 1.91/2.10      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.10  thf('113', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (r1_tarski @ 
% 1.91/2.10              (k10_yellow_6 @ sk_A @ 
% 1.91/2.10               (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) @ 
% 1.91/2.10              (sk_C_1 @ sk_B_1 @ sk_A))))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['111', '112'])).
% 1.91/2.10  thf('114', plain,
% 1.91/2.10      (((~ (r1_tarski @ k1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['96', '113'])).
% 1.91/2.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.91/2.10  thf('115', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.91/2.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.91/2.10  thf('116', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['114', '115'])).
% 1.91/2.10  thf('117', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['116'])).
% 1.91/2.10  thf('118', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['51', '52'])).
% 1.91/2.10  thf('119', plain,
% 1.91/2.10      ((![X36 : $i]:
% 1.91/2.10          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A)))
% 1.91/2.10         <= ((![X36 : $i]:
% 1.91/2.10                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 1.91/2.10                 | ~ (v3_yellow_6 @ X36 @ sk_A))))),
% 1.91/2.10      inference('split', [status(esa)], ['2'])).
% 1.91/2.10  thf('120', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v3_yellow_6 @ 
% 1.91/2.10              (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ sk_A)))
% 1.91/2.10         <= ((![X36 : $i]:
% 1.91/2.10                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 1.91/2.10                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 1.91/2.10             ((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['118', '119'])).
% 1.91/2.10  thf('121', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= ((![X36 : $i]:
% 1.91/2.10                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 1.91/2.10                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 1.91/2.10             ((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['117', '120'])).
% 1.91/2.10  thf('122', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= ((![X36 : $i]:
% 1.91/2.10                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 1.91/2.10                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 1.91/2.10             ((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['121'])).
% 1.91/2.10  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.10  thf('124', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 1.91/2.10         <= ((![X36 : $i]:
% 1.91/2.10                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 1.91/2.10                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 1.91/2.10             ((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['122', '123'])).
% 1.91/2.10  thf('125', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 1.91/2.10            sk_A @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('clc', [status(thm)], ['51', '52'])).
% 1.91/2.10  thf('126', plain,
% 1.91/2.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.10         (~ (l1_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X16)
% 1.91/2.10          | (v2_struct_0 @ X17)
% 1.91/2.10          | ~ (v4_orders_2 @ X17)
% 1.91/2.10          | ~ (v7_waybel_0 @ X17)
% 1.91/2.10          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.10          | ~ (v2_struct_0 @ X18)
% 1.91/2.10          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.10      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.10  thf('127', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 1.91/2.10         | ~ (v7_waybel_0 @ sk_B_1)
% 1.91/2.10         | ~ (v4_orders_2 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('sup-', [status(thm)], ['125', '126'])).
% 1.91/2.10  thf('128', plain,
% 1.91/2.10      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 1.91/2.10      inference('split', [status(esa)], ['4'])).
% 1.91/2.10  thf('129', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['6'])).
% 1.91/2.10  thf('130', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('split', [status(esa)], ['8'])).
% 1.91/2.10  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.10      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.10  thf('132', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.10         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)
% 1.91/2.10         | (v2_struct_0 @ sk_A)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 1.91/2.10  thf('133', plain,
% 1.91/2.10      ((((v2_struct_0 @ sk_A)
% 1.91/2.10         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 1.91/2.10         | (v2_struct_0 @ sk_B_1)))
% 1.91/2.10         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.10             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.10             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.10             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.10      inference('simplify', [status(thm)], ['132'])).
% 1.91/2.11  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('135', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_B_1)
% 1.91/2.11         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 1.91/2.11         <= (((v1_compts_1 @ sk_A)) & 
% 1.91/2.11             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.11             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.11             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.11      inference('clc', [status(thm)], ['133', '134'])).
% 1.91/2.11  thf('136', plain,
% 1.91/2.11      (((v2_struct_0 @ sk_B_1))
% 1.91/2.11         <= ((![X36 : $i]:
% 1.91/2.11                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 1.91/2.11                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 1.91/2.11             ((v1_compts_1 @ sk_A)) & 
% 1.91/2.11             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 1.91/2.11             ((v7_waybel_0 @ sk_B_1)) & 
% 1.91/2.11             ((v4_orders_2 @ sk_B_1)))),
% 1.91/2.11      inference('clc', [status(thm)], ['124', '135'])).
% 1.91/2.11  thf('137', plain,
% 1.91/2.11      ((~ (v2_struct_0 @ sk_B_1)) <= (~ ((v2_struct_0 @ sk_B_1)))),
% 1.91/2.11      inference('split', [status(esa)], ['10'])).
% 1.91/2.11  thf('138', plain,
% 1.91/2.11      (~ ((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A)) | 
% 1.91/2.11       ~
% 1.91/2.11       (![X36 : $i]:
% 1.91/2.11          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 1.91/2.11       ~ ((v7_waybel_0 @ sk_B_1)) | ~ ((v4_orders_2 @ sk_B_1)) | 
% 1.91/2.11       ((v2_struct_0 @ sk_B_1))),
% 1.91/2.11      inference('sup-', [status(thm)], ['136', '137'])).
% 1.91/2.11  thf('139', plain,
% 1.91/2.11      ((![X37 : $i]:
% 1.91/2.11          ((v2_struct_0 @ X37)
% 1.91/2.11           | ~ (v4_orders_2 @ X37)
% 1.91/2.11           | ~ (v7_waybel_0 @ X37)
% 1.91/2.11           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11           | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) | 
% 1.91/2.11       ((v1_compts_1 @ sk_A))),
% 1.91/2.11      inference('split', [status(esa)], ['13'])).
% 1.91/2.11  thf(t36_yellow19, axiom,
% 1.91/2.11    (![A:$i]:
% 1.91/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.11       ( ( v1_compts_1 @ A ) <=>
% 1.91/2.11         ( ![B:$i]:
% 1.91/2.11           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.11               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.11             ( ~( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) ) & 
% 1.91/2.11                  ( ![C:$i]:
% 1.91/2.11                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.91/2.11                      ( ~( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ) ) ) ))).
% 1.91/2.11  thf('140', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v7_waybel_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('141', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v4_orders_2 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('142', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v7_waybel_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('143', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v4_orders_2 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('144', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('145', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v4_orders_2 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('146', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v7_waybel_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('147', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('148', plain,
% 1.91/2.11      ((![X37 : $i]:
% 1.91/2.11          ((v2_struct_0 @ X37)
% 1.91/2.11           | ~ (v4_orders_2 @ X37)
% 1.91/2.11           | ~ (v7_waybel_0 @ X37)
% 1.91/2.11           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11           | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('split', [status(esa)], ['0'])).
% 1.91/2.11  thf('149', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['147', '148'])).
% 1.91/2.11  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('152', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['149', '150', '151'])).
% 1.91/2.11  thf('153', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['146', '152'])).
% 1.91/2.11  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('156', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['153', '154', '155'])).
% 1.91/2.11  thf('157', plain,
% 1.91/2.11      ((((m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['156'])).
% 1.91/2.11  thf('158', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['145', '157'])).
% 1.91/2.11  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('161', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['158', '159', '160'])).
% 1.91/2.11  thf('162', plain,
% 1.91/2.11      ((((m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['161'])).
% 1.91/2.11  thf('163', plain,
% 1.91/2.11      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.11         (~ (l1_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X17)
% 1.91/2.11          | ~ (v4_orders_2 @ X17)
% 1.91/2.11          | ~ (v7_waybel_0 @ X17)
% 1.91/2.11          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.11          | (v7_waybel_0 @ X18)
% 1.91/2.11          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.11      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.11  thf('164', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['162', '163'])).
% 1.91/2.11  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.11      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.11  thf('166', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['164', '165'])).
% 1.91/2.11  thf('167', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['166'])).
% 1.91/2.11  thf('168', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['144', '167'])).
% 1.91/2.11  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('171', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['168', '169', '170'])).
% 1.91/2.11  thf('172', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['171'])).
% 1.91/2.11  thf('173', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['143', '172'])).
% 1.91/2.11  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('176', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['173', '174', '175'])).
% 1.91/2.11  thf('177', plain,
% 1.91/2.11      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['176'])).
% 1.91/2.11  thf('178', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['142', '177'])).
% 1.91/2.11  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('181', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['178', '179', '180'])).
% 1.91/2.11  thf('182', plain,
% 1.91/2.11      ((((v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['181'])).
% 1.91/2.11  thf('183', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v4_orders_2 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('184', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v7_waybel_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('185', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('186', plain,
% 1.91/2.11      ((((m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['161'])).
% 1.91/2.11  thf('187', plain,
% 1.91/2.11      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.11         (~ (l1_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X17)
% 1.91/2.11          | ~ (v4_orders_2 @ X17)
% 1.91/2.11          | ~ (v7_waybel_0 @ X17)
% 1.91/2.11          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.11          | (v4_orders_2 @ X18)
% 1.91/2.11          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.11      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.11  thf('188', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['186', '187'])).
% 1.91/2.11  thf('189', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.11      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.11  thf('190', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['188', '189'])).
% 1.91/2.11  thf('191', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['190'])).
% 1.91/2.11  thf('192', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['185', '191'])).
% 1.91/2.11  thf('193', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('195', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['192', '193', '194'])).
% 1.91/2.11  thf('196', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['195'])).
% 1.91/2.11  thf('197', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['184', '196'])).
% 1.91/2.11  thf('198', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('200', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['197', '198', '199'])).
% 1.91/2.11  thf('201', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['200'])).
% 1.91/2.11  thf('202', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['183', '201'])).
% 1.91/2.11  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('205', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['202', '203', '204'])).
% 1.91/2.11  thf('206', plain,
% 1.91/2.11      ((((v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['205'])).
% 1.91/2.11  thf('207', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v4_orders_2 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('208', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v7_waybel_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('209', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('210', plain,
% 1.91/2.11      ((![X37 : $i]:
% 1.91/2.11          ((v2_struct_0 @ X37)
% 1.91/2.11           | ~ (v4_orders_2 @ X37)
% 1.91/2.11           | ~ (v7_waybel_0 @ X37)
% 1.91/2.11           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11           | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('split', [status(esa)], ['13'])).
% 1.91/2.11  thf('211', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['209', '210'])).
% 1.91/2.11  thf('212', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('214', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('demod', [status(thm)], ['211', '212', '213'])).
% 1.91/2.11  thf('215', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['208', '214'])).
% 1.91/2.11  thf('216', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('218', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('demod', [status(thm)], ['215', '216', '217'])).
% 1.91/2.11  thf('219', plain,
% 1.91/2.11      ((((v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['218'])).
% 1.91/2.11  thf('220', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['207', '219'])).
% 1.91/2.11  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('223', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('demod', [status(thm)], ['220', '221', '222'])).
% 1.91/2.11  thf('224', plain,
% 1.91/2.11      ((((v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['223'])).
% 1.91/2.11  thf('225', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v7_waybel_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('226', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v4_orders_2 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('227', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('228', plain,
% 1.91/2.11      ((((m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['161'])).
% 1.91/2.11  thf('229', plain,
% 1.91/2.11      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.11         (~ (l1_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X17)
% 1.91/2.11          | ~ (v4_orders_2 @ X17)
% 1.91/2.11          | ~ (v7_waybel_0 @ X17)
% 1.91/2.11          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.11          | (l1_waybel_0 @ X18 @ X16)
% 1.91/2.11          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.11      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.11  thf('230', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['228', '229'])).
% 1.91/2.11  thf('231', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.11      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.11  thf('232', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['230', '231'])).
% 1.91/2.11  thf('233', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['232'])).
% 1.91/2.11  thf('234', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['227', '233'])).
% 1.91/2.11  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('237', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['234', '235', '236'])).
% 1.91/2.11  thf('238', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['237'])).
% 1.91/2.11  thf('239', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['226', '238'])).
% 1.91/2.11  thf('240', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('242', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['239', '240', '241'])).
% 1.91/2.11  thf('243', plain,
% 1.91/2.11      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['242'])).
% 1.91/2.11  thf('244', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['225', '243'])).
% 1.91/2.11  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('247', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['244', '245', '246'])).
% 1.91/2.11  thf('248', plain,
% 1.91/2.11      ((((l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['247'])).
% 1.91/2.11  thf('249', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v7_waybel_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('250', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((v4_orders_2 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('251', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('252', plain,
% 1.91/2.11      ((((m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['161'])).
% 1.91/2.11  thf('253', plain,
% 1.91/2.11      ((((v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['205'])).
% 1.91/2.11  thf('254', plain,
% 1.91/2.11      ((((v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['181'])).
% 1.91/2.11  thf('255', plain,
% 1.91/2.11      ((((l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['247'])).
% 1.91/2.11  thf(d3_tarski, axiom,
% 1.91/2.11    (![A:$i,B:$i]:
% 1.91/2.11     ( ( r1_tarski @ A @ B ) <=>
% 1.91/2.11       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.91/2.11  thf('256', plain,
% 1.91/2.11      (![X1 : $i, X3 : $i]:
% 1.91/2.11         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.91/2.11      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.11  thf('257', plain,
% 1.91/2.11      ((((v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['181'])).
% 1.91/2.11  thf('258', plain,
% 1.91/2.11      ((((v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['205'])).
% 1.91/2.11  thf('259', plain,
% 1.91/2.11      ((((l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['247'])).
% 1.91/2.11  thf(dt_k10_yellow_6, axiom,
% 1.91/2.11    (![A:$i,B:$i]:
% 1.91/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.91/2.11         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.91/2.11         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.11       ( m1_subset_1 @
% 1.91/2.11         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.91/2.11  thf('260', plain,
% 1.91/2.11      (![X14 : $i, X15 : $i]:
% 1.91/2.11         (~ (l1_pre_topc @ X14)
% 1.91/2.11          | ~ (v2_pre_topc @ X14)
% 1.91/2.11          | (v2_struct_0 @ X14)
% 1.91/2.11          | (v2_struct_0 @ X15)
% 1.91/2.11          | ~ (v4_orders_2 @ X15)
% 1.91/2.11          | ~ (v7_waybel_0 @ X15)
% 1.91/2.11          | ~ (l1_waybel_0 @ X15 @ X14)
% 1.91/2.11          | (m1_subset_1 @ (k10_yellow_6 @ X14 @ X15) @ 
% 1.91/2.11             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 1.91/2.11      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 1.91/2.11  thf('261', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ 
% 1.91/2.11            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['259', '260'])).
% 1.91/2.11  thf('262', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('263', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('264', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ 
% 1.91/2.11            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['261', '262', '263'])).
% 1.91/2.11  thf('265', plain,
% 1.91/2.11      ((((v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ 
% 1.91/2.11            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['264'])).
% 1.91/2.11  thf('266', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ 
% 1.91/2.11            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['258', '265'])).
% 1.91/2.11  thf('267', plain,
% 1.91/2.11      ((((v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ 
% 1.91/2.11            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['266'])).
% 1.91/2.11  thf('268', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ 
% 1.91/2.11            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['257', '267'])).
% 1.91/2.11  thf('269', plain,
% 1.91/2.11      ((((v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ 
% 1.91/2.11            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['268'])).
% 1.91/2.11  thf(t4_subset, axiom,
% 1.91/2.11    (![A:$i,B:$i,C:$i]:
% 1.91/2.11     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.91/2.11       ( m1_subset_1 @ A @ C ) ))).
% 1.91/2.11  thf('270', plain,
% 1.91/2.11      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.91/2.11         (~ (r2_hidden @ X8 @ X9)
% 1.91/2.11          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 1.91/2.11          | (m1_subset_1 @ X8 @ X10))),
% 1.91/2.11      inference('cnf', [status(esa)], [t4_subset])).
% 1.91/2.11  thf('271', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.91/2.11           | ~ (r2_hidden @ X0 @ 
% 1.91/2.11                (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['269', '270'])).
% 1.91/2.11  thf('272', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (m1_subset_1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))) @ 
% 1.91/2.11              (u1_struct_0 @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['256', '271'])).
% 1.91/2.11  thf('273', plain,
% 1.91/2.11      (![X1 : $i, X3 : $i]:
% 1.91/2.11         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.91/2.11      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.11  thf(t29_waybel_9, axiom,
% 1.91/2.11    (![A:$i]:
% 1.91/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.11       ( ![B:$i]:
% 1.91/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.11             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.11           ( ![C:$i]:
% 1.91/2.11             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.91/2.11               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) =>
% 1.91/2.11                 ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 1.91/2.11  thf('274', plain,
% 1.91/2.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.91/2.11         ((v2_struct_0 @ X21)
% 1.91/2.11          | ~ (v4_orders_2 @ X21)
% 1.91/2.11          | ~ (v7_waybel_0 @ X21)
% 1.91/2.11          | ~ (l1_waybel_0 @ X21 @ X22)
% 1.91/2.11          | ~ (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 1.91/2.11          | (r3_waybel_9 @ X22 @ X21 @ X23)
% 1.91/2.11          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 1.91/2.11          | ~ (l1_pre_topc @ X22)
% 1.91/2.11          | ~ (v2_pre_topc @ X22)
% 1.91/2.11          | (v2_struct_0 @ X22))),
% 1.91/2.11      inference('cnf', [status(esa)], [t29_waybel_9])).
% 1.91/2.11  thf('275', plain,
% 1.91/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.11         ((r1_tarski @ (k10_yellow_6 @ X1 @ X0) @ X2)
% 1.91/2.11          | (v2_struct_0 @ X1)
% 1.91/2.11          | ~ (v2_pre_topc @ X1)
% 1.91/2.11          | ~ (l1_pre_topc @ X1)
% 1.91/2.11          | ~ (m1_subset_1 @ (sk_C @ X2 @ (k10_yellow_6 @ X1 @ X0)) @ 
% 1.91/2.11               (u1_struct_0 @ X1))
% 1.91/2.11          | (r3_waybel_9 @ X1 @ X0 @ (sk_C @ X2 @ (k10_yellow_6 @ X1 @ X0)))
% 1.91/2.11          | ~ (l1_waybel_0 @ X0 @ X1)
% 1.91/2.11          | ~ (v7_waybel_0 @ X0)
% 1.91/2.11          | ~ (v4_orders_2 @ X0)
% 1.91/2.11          | (v2_struct_0 @ X0))),
% 1.91/2.11      inference('sup-', [status(thm)], ['273', '274'])).
% 1.91/2.11  thf('276', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['272', '275'])).
% 1.91/2.11  thf('277', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('278', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('279', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['276', '277', '278'])).
% 1.91/2.11  thf('280', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['279'])).
% 1.91/2.11  thf('281', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['255', '280'])).
% 1.91/2.11  thf('282', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['281'])).
% 1.91/2.11  thf('283', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['254', '282'])).
% 1.91/2.11  thf('284', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['283'])).
% 1.91/2.11  thf('285', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['253', '284'])).
% 1.91/2.11  thf('286', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r3_waybel_9 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)) @ 
% 1.91/2.11            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['285'])).
% 1.91/2.11  thf('287', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (m1_subset_1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))) @ 
% 1.91/2.11              (u1_struct_0 @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['256', '271'])).
% 1.91/2.11  thf(t31_waybel_9, axiom,
% 1.91/2.11    (![A:$i]:
% 1.91/2.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.91/2.11       ( ![B:$i]:
% 1.91/2.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 1.91/2.11             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 1.91/2.11           ( ![C:$i]:
% 1.91/2.11             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 1.91/2.11               ( ![D:$i]:
% 1.91/2.11                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.91/2.11                   ( ( r3_waybel_9 @ A @ C @ D ) => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 1.91/2.11  thf('288', plain,
% 1.91/2.11      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.91/2.11         ((v2_struct_0 @ X24)
% 1.91/2.11          | ~ (v4_orders_2 @ X24)
% 1.91/2.11          | ~ (v7_waybel_0 @ X24)
% 1.91/2.11          | ~ (l1_waybel_0 @ X24 @ X25)
% 1.91/2.11          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 1.91/2.11          | (r3_waybel_9 @ X25 @ X24 @ X26)
% 1.91/2.11          | ~ (r3_waybel_9 @ X25 @ X27 @ X26)
% 1.91/2.11          | ~ (m2_yellow_6 @ X27 @ X25 @ X24)
% 1.91/2.11          | ~ (l1_pre_topc @ X25)
% 1.91/2.11          | ~ (v2_pre_topc @ X25)
% 1.91/2.11          | (v2_struct_0 @ X25))),
% 1.91/2.11      inference('cnf', [status(esa)], [t31_waybel_9])).
% 1.91/2.11  thf('289', plain,
% 1.91/2.11      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11           | ~ (m2_yellow_6 @ X2 @ sk_A @ X1)
% 1.91/2.11           | ~ (r3_waybel_9 @ sk_A @ X2 @ 
% 1.91/2.11                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ X1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 1.91/2.11           | ~ (v7_waybel_0 @ X1)
% 1.91/2.11           | ~ (v4_orders_2 @ X1)
% 1.91/2.11           | (v2_struct_0 @ X1)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['287', '288'])).
% 1.91/2.11  thf('290', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('291', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('292', plain,
% 1.91/2.11      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | ~ (m2_yellow_6 @ X2 @ sk_A @ X1)
% 1.91/2.11           | ~ (r3_waybel_9 @ sk_A @ X2 @ 
% 1.91/2.11                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ X1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 1.91/2.11           | ~ (v7_waybel_0 @ X1)
% 1.91/2.11           | ~ (v4_orders_2 @ X1)
% 1.91/2.11           | (v2_struct_0 @ X1)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['289', '290', '291'])).
% 1.91/2.11  thf('293', plain,
% 1.91/2.11      ((![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.11          ((v2_struct_0 @ X1)
% 1.91/2.11           | ~ (v4_orders_2 @ X1)
% 1.91/2.11           | ~ (v7_waybel_0 @ X1)
% 1.91/2.11           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ X1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (r3_waybel_9 @ sk_A @ X2 @ 
% 1.91/2.11                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (m2_yellow_6 @ X2 @ sk_A @ X1)
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['292'])).
% 1.91/2.11  thf('294', plain,
% 1.91/2.11      ((![X0 : $i, X1 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | ~ (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ X1)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ X1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 1.91/2.11           | ~ (v7_waybel_0 @ X1)
% 1.91/2.11           | ~ (v4_orders_2 @ X1)
% 1.91/2.11           | (v2_struct_0 @ X1)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['286', '293'])).
% 1.91/2.11  thf('295', plain,
% 1.91/2.11      ((![X0 : $i, X1 : $i]:
% 1.91/2.11          ((v2_struct_0 @ X1)
% 1.91/2.11           | ~ (v4_orders_2 @ X1)
% 1.91/2.11           | ~ (v7_waybel_0 @ X1)
% 1.91/2.11           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ X1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ X1)
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['294'])).
% 1.91/2.11  thf('296', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['252', '295'])).
% 1.91/2.11  thf('297', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          (~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11           | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['296'])).
% 1.91/2.11  thf('298', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['251', '297'])).
% 1.91/2.11  thf('299', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('300', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('301', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11           | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['298', '299', '300'])).
% 1.91/2.11  thf('302', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          (~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['301'])).
% 1.91/2.11  thf('303', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['250', '302'])).
% 1.91/2.11  thf('304', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('305', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('306', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['303', '304', '305'])).
% 1.91/2.11  thf('307', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          (~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['306'])).
% 1.91/2.11  thf('308', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['249', '307'])).
% 1.91/2.11  thf('309', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('310', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('311', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['308', '309', '310'])).
% 1.91/2.11  thf('312', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['311'])).
% 1.91/2.11  thf('313', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (m1_subset_1 @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))) @ 
% 1.91/2.11              (u1_struct_0 @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['256', '271'])).
% 1.91/2.11  thf('314', plain,
% 1.91/2.11      (![X33 : $i, X34 : $i]:
% 1.91/2.11         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 1.91/2.11          | ~ (r3_waybel_9 @ X33 @ (sk_B @ X33) @ X34)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('315', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11           | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['313', '314'])).
% 1.91/2.11  thf('316', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('317', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('318', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['315', '316', '317'])).
% 1.91/2.11  thf('319', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          (~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 1.91/2.11              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['318'])).
% 1.91/2.11  thf('320', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ sk_A)
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['312', '319'])).
% 1.91/2.11  thf('321', plain,
% 1.91/2.11      ((![X0 : $i]:
% 1.91/2.11          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) @ X0)
% 1.91/2.11           | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11           | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11           | (v1_compts_1 @ sk_A)
% 1.91/2.11           | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['320'])).
% 1.91/2.11  thf('322', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 1.91/2.11      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.91/2.11  thf(d10_xboole_0, axiom,
% 1.91/2.11    (![A:$i,B:$i]:
% 1.91/2.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.11  thf('323', plain,
% 1.91/2.11      (![X4 : $i, X6 : $i]:
% 1.91/2.11         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.91/2.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.91/2.11  thf('324', plain,
% 1.91/2.11      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.91/2.11      inference('sup-', [status(thm)], ['322', '323'])).
% 1.91/2.11  thf('325', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ((k10_yellow_6 @ sk_A @ (sk_C_3 @ (sk_B @ sk_A))) = (k1_xboole_0))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['321', '324'])).
% 1.91/2.11  thf('326', plain,
% 1.91/2.11      (![X19 : $i, X20 : $i]:
% 1.91/2.11         ((v2_struct_0 @ X19)
% 1.91/2.11          | ~ (v4_orders_2 @ X19)
% 1.91/2.11          | ~ (v7_waybel_0 @ X19)
% 1.91/2.11          | ~ (l1_waybel_0 @ X19 @ X20)
% 1.91/2.11          | ~ (v3_yellow_6 @ X19 @ X20)
% 1.91/2.11          | ((k10_yellow_6 @ X20 @ X19) != (k1_xboole_0))
% 1.91/2.11          | ~ (l1_pre_topc @ X20)
% 1.91/2.11          | ~ (v2_pre_topc @ X20)
% 1.91/2.11          | (v2_struct_0 @ X20))),
% 1.91/2.11      inference('cnf', [status(esa)], [d19_yellow_6])).
% 1.91/2.11  thf('327', plain,
% 1.91/2.11      (((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | ~ (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['325', '326'])).
% 1.91/2.11  thf('328', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('329', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('330', plain,
% 1.91/2.11      (((((k1_xboole_0) != (k1_xboole_0))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['327', '328', '329'])).
% 1.91/2.11  thf('331', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['330'])).
% 1.91/2.11  thf('332', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['248', '331'])).
% 1.91/2.11  thf('333', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v3_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['332'])).
% 1.91/2.11  thf('334', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['224', '333'])).
% 1.91/2.11  thf('335', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['334'])).
% 1.91/2.11  thf('336', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['206', '335'])).
% 1.91/2.11  thf('337', plain,
% 1.91/2.11      (((~ (v7_waybel_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['336'])).
% 1.91/2.11  thf('338', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['182', '337'])).
% 1.91/2.11  thf('339', plain,
% 1.91/2.11      ((((v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['338'])).
% 1.91/2.11  thf('340', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('341', plain,
% 1.91/2.11      ((((m2_yellow_6 @ (sk_C_3 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['161'])).
% 1.91/2.11  thf('342', plain,
% 1.91/2.11      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.11         (~ (l1_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X16)
% 1.91/2.11          | (v2_struct_0 @ X17)
% 1.91/2.11          | ~ (v4_orders_2 @ X17)
% 1.91/2.11          | ~ (v7_waybel_0 @ X17)
% 1.91/2.11          | ~ (l1_waybel_0 @ X17 @ X16)
% 1.91/2.11          | ~ (v2_struct_0 @ X18)
% 1.91/2.11          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 1.91/2.11      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 1.91/2.11  thf('343', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (l1_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['341', '342'])).
% 1.91/2.11  thf('344', plain, ((l1_struct_0 @ sk_A)),
% 1.91/2.11      inference('sup-', [status(thm)], ['59', '60'])).
% 1.91/2.11  thf('345', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['343', '344'])).
% 1.91/2.11  thf('346', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 1.91/2.11         | ~ (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['345'])).
% 1.91/2.11  thf('347', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['340', '346'])).
% 1.91/2.11  thf('348', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('349', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('350', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['347', '348', '349'])).
% 1.91/2.11  thf('351', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v2_struct_0 @ (sk_C_3 @ (sk_B @ sk_A)))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['350'])).
% 1.91/2.11  thf('352', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['339', '351'])).
% 1.91/2.11  thf('353', plain,
% 1.91/2.11      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['352'])).
% 1.91/2.11  thf('354', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['141', '353'])).
% 1.91/2.11  thf('355', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('356', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('357', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['354', '355', '356'])).
% 1.91/2.11  thf('358', plain,
% 1.91/2.11      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['357'])).
% 1.91/2.11  thf('359', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['140', '358'])).
% 1.91/2.11  thf('360', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('361', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('362', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['359', '360', '361'])).
% 1.91/2.11  thf('363', plain,
% 1.91/2.11      ((((v2_struct_0 @ (sk_B @ sk_A))
% 1.91/2.11         | (v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['362'])).
% 1.91/2.11  thf('364', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('365', plain,
% 1.91/2.11      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ (sk_B @ sk_A))))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('clc', [status(thm)], ['363', '364'])).
% 1.91/2.11  thf('366', plain,
% 1.91/2.11      (![X33 : $i]:
% 1.91/2.11         (~ (v2_struct_0 @ (sk_B @ X33))
% 1.91/2.11          | (v1_compts_1 @ X33)
% 1.91/2.11          | ~ (l1_pre_topc @ X33)
% 1.91/2.11          | ~ (v2_pre_topc @ X33)
% 1.91/2.11          | (v2_struct_0 @ X33))),
% 1.91/2.11      inference('cnf', [status(esa)], [t36_yellow19])).
% 1.91/2.11  thf('367', plain,
% 1.91/2.11      ((((v1_compts_1 @ sk_A)
% 1.91/2.11         | (v2_struct_0 @ sk_A)
% 1.91/2.11         | ~ (v2_pre_topc @ sk_A)
% 1.91/2.11         | ~ (l1_pre_topc @ sk_A)
% 1.91/2.11         | (v1_compts_1 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('sup-', [status(thm)], ['365', '366'])).
% 1.91/2.11  thf('368', plain, ((v2_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('369', plain, ((l1_pre_topc @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('370', plain,
% 1.91/2.11      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('demod', [status(thm)], ['367', '368', '369'])).
% 1.91/2.11  thf('371', plain,
% 1.91/2.11      ((((v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('simplify', [status(thm)], ['370'])).
% 1.91/2.11  thf('372', plain, (~ (v2_struct_0 @ sk_A)),
% 1.91/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.11  thf('373', plain,
% 1.91/2.11      (((v1_compts_1 @ sk_A))
% 1.91/2.11         <= ((![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) & 
% 1.91/2.11             (![X37 : $i]:
% 1.91/2.11                ((v2_struct_0 @ X37)
% 1.91/2.11                 | ~ (v4_orders_2 @ X37)
% 1.91/2.11                 | ~ (v7_waybel_0 @ X37)
% 1.91/2.11                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11                 | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37))))),
% 1.91/2.11      inference('clc', [status(thm)], ['371', '372'])).
% 1.91/2.11  thf('374', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 1.91/2.11      inference('split', [status(esa)], ['2'])).
% 1.91/2.11  thf('375', plain,
% 1.91/2.11      (~
% 1.91/2.11       (![X37 : $i]:
% 1.91/2.11          ((v2_struct_0 @ X37)
% 1.91/2.11           | ~ (v4_orders_2 @ X37)
% 1.91/2.11           | ~ (v7_waybel_0 @ X37)
% 1.91/2.11           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11           | (v3_yellow_6 @ (sk_C_3 @ X37) @ sk_A))) | 
% 1.91/2.11       ((v1_compts_1 @ sk_A)) | 
% 1.91/2.11       ~
% 1.91/2.11       (![X37 : $i]:
% 1.91/2.11          ((v2_struct_0 @ X37)
% 1.91/2.11           | ~ (v4_orders_2 @ X37)
% 1.91/2.11           | ~ (v7_waybel_0 @ X37)
% 1.91/2.11           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 1.91/2.11           | (m2_yellow_6 @ (sk_C_3 @ X37) @ sk_A @ X37)))),
% 1.91/2.11      inference('sup-', [status(thm)], ['373', '374'])).
% 1.93/2.11  thf('376', plain, ($false),
% 1.93/2.11      inference('sat_resolution*', [status(thm)],
% 1.93/2.11                ['1', '3', '5', '7', '9', '11', '138', '139', '375'])).
% 1.93/2.11  
% 1.93/2.11  % SZS output end Refutation
% 1.93/2.11  
% 1.93/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
