%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a1B7Yq3Uov

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:58 EST 2020

% Result     : Theorem 12.90s
% Output     : Refutation 12.90s
% Verified   : 
% Statistics : Number of formulae       :  490 (4120 expanded)
%              Number of leaves         :   43 (1109 expanded)
%              Depth                    :  108
%              Number of atoms          : 11995 (88893 expanded)
%              Number of equality atoms :   84 ( 124 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k6_yellow_6_type,type,(
    k6_yellow_6: $i > $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
      | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) )
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
      | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A )
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
      | ( r3_waybel_9 @ X31 @ X32 @ ( sk_C @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('18',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_C @ X32 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m2_yellow_6 @ ( sk_D_1 @ X30 @ X28 @ X29 ) @ X29 @ X28 )
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
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) @ sk_A @ X0 )
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
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) @ sk_A @ X0 )
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
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
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
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 )
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
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
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
      | ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
      | ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
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
      | ( v7_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
      | ( v7_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
      | ( v7_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
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
      | ( l1_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
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
      | ( l1_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
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
      | ( l1_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
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
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
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
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v4_orders_2 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','94'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('98',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( r2_hidden @ X30 @ ( k10_yellow_6 @ X29 @ ( sk_D_1 @ X30 @ X28 @ X29 ) ) )
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
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ) )
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
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_1 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ X0 @ sk_A ) ) )
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
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
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
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
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
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) ) )
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
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
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
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
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
      | ~ ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
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
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
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
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
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
      | ~ ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
      | ~ ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
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
      | ~ ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
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
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('190',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) ) ),
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
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('232',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('253',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('254',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('255',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('256',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('257',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('258',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('259',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d18_yellow_6,axiom,(
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
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k10_yellow_6 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ! [E: $i] :
                          ( ( m1_connsp_2 @ E @ A @ D )
                         => ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) )).

thf('260',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X8 @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ( X10
        = ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X1 @ X0 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['258','261'])).

thf('263',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['257','266'])).

thf('268',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['256','268'])).

thf('270',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('271',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('272',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('273',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('274',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('275',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('276',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('277',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('278',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('279',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('280',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('281',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
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

thf('282',plain,(
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

thf('283',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['283','284','285'])).

thf('287',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['286'])).

thf('288',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['280','287'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['279','289'])).

thf('291',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( X10
       != ( k10_yellow_6 @ X9 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X12 @ X8 @ X9 ) @ X9 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('293',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X9 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X12 @ X8 @ X9 ) @ X9 @ X12 )
      | ( r2_hidden @ X12 @ ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['291','293'])).

thf('295',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['294','295','296'])).

thf('298',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['278','298'])).

thf('300',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['277','300'])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['276','302'])).

thf('304',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['275','304'])).

thf('306',plain,
    ( ( ( m1_connsp_2 @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('308',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_D @ X10 @ X8 @ X9 ) @ X10 )
      | ( r1_waybel_0 @ X9 @ X8 @ X11 )
      | ~ ( m1_connsp_2 @ X11 @ X9 @ ( sk_D @ X10 @ X8 @ X9 ) )
      | ( X10
        = ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('309',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ X0 @ X1 ) )
      | ~ ( m1_connsp_2 @ X2 @ X0 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) )
      | ( r1_waybel_0 @ X0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      | ~ ( l1_waybel_0 @ X1 @ X0 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['306','309'])).

thf('311',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['310','311','312'])).

thf('314',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['313'])).

thf('315',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['274','314'])).

thf('316',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['273','316'])).

thf('318',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['272','318'])).

thf('320',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('322',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('323',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('324',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('325',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( X10
       != ( k10_yellow_6 @ X9 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ ( sk_E_1 @ X12 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('326',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X9 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_waybel_0 @ X9 @ X8 @ ( sk_E_1 @ X12 @ X8 @ X9 ) )
      | ( r2_hidden @ X12 @ ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['324','326'])).

thf('328',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['327','328','329'])).

thf('331',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['323','331'])).

thf('333',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['322','333'])).

thf('335',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['321','335'])).

thf('337',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['320','337'])).

thf('339',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['338'])).

thf('340',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['271','339'])).

thf('341',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['340'])).

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

thf('342',plain,(
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

thf('343',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('345',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['343','344','345'])).

thf('347',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['346'])).

thf('348',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['270','347'])).

thf('349',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['348'])).

thf('350',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['255','349'])).

thf('351',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['350'])).

thf('352',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['254','351'])).

thf('353',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['253','353'])).

thf('355',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['354'])).

thf('356',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['269'])).

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

thf('357',plain,(
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

thf('358',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('360',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['358','359','360'])).

thf('362',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['355','362'])).

thf('364',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['252','364'])).

thf('366',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['365'])).

thf('367',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['251','366'])).

thf('368',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['367','368','369'])).

thf('371',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['250','371'])).

thf('373',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('374',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['372','373','374'])).

thf('376',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['375'])).

thf('377',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['249','376'])).

thf('378',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('380',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['377','378','379'])).

thf('381',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['380'])).

thf('382',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('383',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r3_waybel_9 @ X33 @ ( sk_B @ X33 ) @ X34 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('384',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['382','383'])).

thf('385',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['384','385','386'])).

thf('388',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['387'])).

thf('389',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['381','388'])).

thf('390',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('392',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['390','391'])).

thf('393',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('394',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['392','393'])).

thf('395',plain,(
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

thf('396',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['394','395'])).

thf('397',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['396','397','398'])).

thf('400',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['399'])).

thf('401',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['248','400'])).

thf('402',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['401'])).

thf('403',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['224','402'])).

thf('404',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['403'])).

thf('405',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['206','404'])).

thf('406',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['182','406'])).

thf('408',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['407'])).

thf('409',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('410',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('411',plain,(
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

thf('412',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['410','411'])).

thf('413',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('414',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['412','413'])).

thf('415',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['414'])).

thf('416',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['409','415'])).

thf('417',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('418',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('419',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['416','417','418'])).

thf('420',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['419'])).

thf('421',plain,
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
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['408','420'])).

thf('422',plain,
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
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['421'])).

thf('423',plain,
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
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['141','422'])).

thf('424',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('426',plain,
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
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['423','424','425'])).

thf('427',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['426'])).

thf('428',plain,
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
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['140','427'])).

thf('429',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('430',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('431',plain,
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
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['428','429','430'])).

thf('432',plain,
    ( ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['431'])).

thf('433',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('434',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(clc,[status(thm)],['432','433'])).

thf('435',plain,(
    ! [X33: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('436',plain,
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
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['434','435'])).

thf('437',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('438',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('439',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['436','437','438'])).

thf('440',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['439'])).

thf('441',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('442',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(clc,[status(thm)],['440','441'])).

thf('443',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('444',plain,
    ( ~ ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ~ ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['442','443'])).

thf('445',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','138','139','444'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a1B7Yq3Uov
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:50:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 12.90/13.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.90/13.13  % Solved by: fo/fo7.sh
% 12.90/13.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.90/13.13  % done 13111 iterations in 12.652s
% 12.90/13.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.90/13.13  % SZS output start Refutation
% 12.90/13.13  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 12.90/13.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 12.90/13.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.90/13.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.90/13.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 12.90/13.13  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 12.90/13.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.90/13.13  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 12.90/13.13  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 12.90/13.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.90/13.13  thf(sk_A_type, type, sk_A: $i).
% 12.90/13.13  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 12.90/13.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 12.90/13.13  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 12.90/13.13  thf(k6_yellow_6_type, type, k6_yellow_6: $i > $i).
% 12.90/13.13  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 12.90/13.13  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 12.90/13.13  thf(sk_B_type, type, sk_B: $i > $i).
% 12.90/13.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.90/13.13  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 12.90/13.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.90/13.13  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 12.90/13.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 12.90/13.13  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 12.90/13.13  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 12.90/13.13  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 12.90/13.13  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 12.90/13.13  thf(sk_B_1_type, type, sk_B_1: $i).
% 12.90/13.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.90/13.13  thf(t37_yellow19, conjecture,
% 12.90/13.13    (![A:$i]:
% 12.90/13.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.13       ( ( v1_compts_1 @ A ) <=>
% 12.90/13.13         ( ![B:$i]:
% 12.90/13.13           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.13               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.13             ( ?[C:$i]:
% 12.90/13.13               ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ))).
% 12.90/13.13  thf(zf_stmt_0, negated_conjecture,
% 12.90/13.13    (~( ![A:$i]:
% 12.90/13.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 12.90/13.13            ( l1_pre_topc @ A ) ) =>
% 12.90/13.13          ( ( v1_compts_1 @ A ) <=>
% 12.90/13.13            ( ![B:$i]:
% 12.90/13.13              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.13                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.13                ( ?[C:$i]:
% 12.90/13.13                  ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ) )),
% 12.90/13.13    inference('cnf.neg', [status(esa)], [t37_yellow19])).
% 12.90/13.13  thf('0', plain,
% 12.90/13.13      (![X37 : $i]:
% 12.90/13.13         ((v2_struct_0 @ X37)
% 12.90/13.13          | ~ (v4_orders_2 @ X37)
% 12.90/13.13          | ~ (v7_waybel_0 @ X37)
% 12.90/13.13          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.13          | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37)
% 12.90/13.13          | (v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('1', plain,
% 12.90/13.13      ((![X37 : $i]:
% 12.90/13.13          ((v2_struct_0 @ X37)
% 12.90/13.13           | ~ (v4_orders_2 @ X37)
% 12.90/13.13           | ~ (v7_waybel_0 @ X37)
% 12.90/13.13           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.13           | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))) | 
% 12.90/13.13       ((v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('split', [status(esa)], ['0'])).
% 12.90/13.13  thf('2', plain,
% 12.90/13.13      (![X36 : $i]:
% 12.90/13.13         (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 12.90/13.13          | ~ (v3_yellow_6 @ X36 @ sk_A)
% 12.90/13.13          | ~ (v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('3', plain,
% 12.90/13.13      ((![X36 : $i]:
% 12.90/13.13          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 12.90/13.13       ~ ((v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('split', [status(esa)], ['2'])).
% 12.90/13.13  thf('4', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('5', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('split', [status(esa)], ['4'])).
% 12.90/13.13  thf('6', plain, (((v7_waybel_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('7', plain, (((v7_waybel_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('split', [status(esa)], ['6'])).
% 12.90/13.13  thf('8', plain, (((v4_orders_2 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('9', plain, (((v4_orders_2 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('split', [status(esa)], ['8'])).
% 12.90/13.13  thf('10', plain, ((~ (v2_struct_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('11', plain, (~ ((v2_struct_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('split', [status(esa)], ['10'])).
% 12.90/13.13  thf('12', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('split', [status(esa)], ['8'])).
% 12.90/13.13  thf('13', plain,
% 12.90/13.13      (![X37 : $i]:
% 12.90/13.13         ((v2_struct_0 @ X37)
% 12.90/13.13          | ~ (v4_orders_2 @ X37)
% 12.90/13.13          | ~ (v7_waybel_0 @ X37)
% 12.90/13.13          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.13          | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A)
% 12.90/13.13          | (v1_compts_1 @ sk_A))),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('14', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 12.90/13.13      inference('split', [status(esa)], ['13'])).
% 12.90/13.13  thf('15', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('split', [status(esa)], ['6'])).
% 12.90/13.13  thf('16', plain,
% 12.90/13.13      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('split', [status(esa)], ['4'])).
% 12.90/13.13  thf(l37_yellow19, axiom,
% 12.90/13.13    (![A:$i]:
% 12.90/13.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.13       ( ( v1_compts_1 @ A ) =>
% 12.90/13.13         ( ![B:$i]:
% 12.90/13.13           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.13               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.13             ( ?[C:$i]:
% 12.90/13.13               ( ( r3_waybel_9 @ A @ B @ C ) & 
% 12.90/13.13                 ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 12.90/13.13  thf('17', plain,
% 12.90/13.13      (![X31 : $i, X32 : $i]:
% 12.90/13.13         (~ (v1_compts_1 @ X31)
% 12.90/13.13          | (v2_struct_0 @ X32)
% 12.90/13.13          | ~ (v4_orders_2 @ X32)
% 12.90/13.13          | ~ (v7_waybel_0 @ X32)
% 12.90/13.13          | ~ (l1_waybel_0 @ X32 @ X31)
% 12.90/13.13          | (r3_waybel_9 @ X31 @ X32 @ (sk_C @ X32 @ X31))
% 12.90/13.13          | ~ (l1_pre_topc @ X31)
% 12.90/13.13          | ~ (v2_pre_topc @ X31)
% 12.90/13.13          | (v2_struct_0 @ X31))),
% 12.90/13.13      inference('cnf', [status(esa)], [l37_yellow19])).
% 12.90/13.13  thf('18', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_A)
% 12.90/13.13         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.13         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.13         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['16', '17'])).
% 12.90/13.13  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('21', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_A)
% 12.90/13.13         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('demod', [status(thm)], ['18', '19', '20'])).
% 12.90/13.13  thf('22', plain,
% 12.90/13.13      (((~ (v1_compts_1 @ sk_A)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13         | (v2_struct_0 @ sk_A)))
% 12.90/13.13         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['15', '21'])).
% 12.90/13.13  thf('23', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_A)
% 12.90/13.13         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['14', '22'])).
% 12.90/13.13  thf('24', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13         | (v2_struct_0 @ sk_A)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['12', '23'])).
% 12.90/13.13  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('26', plain,
% 12.90/13.13      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('clc', [status(thm)], ['24', '25'])).
% 12.90/13.13  thf('27', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('split', [status(esa)], ['8'])).
% 12.90/13.13  thf('28', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 12.90/13.13      inference('split', [status(esa)], ['13'])).
% 12.90/13.13  thf('29', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('split', [status(esa)], ['6'])).
% 12.90/13.13  thf('30', plain,
% 12.90/13.13      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('split', [status(esa)], ['4'])).
% 12.90/13.13  thf('31', plain,
% 12.90/13.13      (![X31 : $i, X32 : $i]:
% 12.90/13.13         (~ (v1_compts_1 @ X31)
% 12.90/13.13          | (v2_struct_0 @ X32)
% 12.90/13.13          | ~ (v4_orders_2 @ X32)
% 12.90/13.13          | ~ (v7_waybel_0 @ X32)
% 12.90/13.13          | ~ (l1_waybel_0 @ X32 @ X31)
% 12.90/13.13          | (m1_subset_1 @ (sk_C @ X32 @ X31) @ (u1_struct_0 @ X31))
% 12.90/13.13          | ~ (l1_pre_topc @ X31)
% 12.90/13.13          | ~ (v2_pre_topc @ X31)
% 12.90/13.13          | (v2_struct_0 @ X31))),
% 12.90/13.13      inference('cnf', [status(esa)], [l37_yellow19])).
% 12.90/13.13  thf('32', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_A)
% 12.90/13.13         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.13         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.13         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.90/13.13         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['30', '31'])).
% 12.90/13.13  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('35', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_A)
% 12.90/13.13         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.90/13.13         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('demod', [status(thm)], ['32', '33', '34'])).
% 12.90/13.13  thf('36', plain,
% 12.90/13.13      (((~ (v1_compts_1 @ sk_A)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.90/13.13         | (v2_struct_0 @ sk_A)))
% 12.90/13.13         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['29', '35'])).
% 12.90/13.13  thf('37', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_A)
% 12.90/13.13         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['28', '36'])).
% 12.90/13.13  thf('38', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.90/13.13         | (v2_struct_0 @ sk_A)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['27', '37'])).
% 12.90/13.13  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('40', plain,
% 12.90/13.13      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('clc', [status(thm)], ['38', '39'])).
% 12.90/13.13  thf(t32_waybel_9, axiom,
% 12.90/13.13    (![A:$i]:
% 12.90/13.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.13       ( ![B:$i]:
% 12.90/13.13         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.13             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.13           ( ![C:$i]:
% 12.90/13.13             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.90/13.13               ( ~( ( r3_waybel_9 @ A @ B @ C ) & 
% 12.90/13.13                    ( ![D:$i]:
% 12.90/13.13                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 12.90/13.13                        ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.90/13.13  thf('41', plain,
% 12.90/13.13      (![X28 : $i, X29 : $i, X30 : $i]:
% 12.90/13.13         ((v2_struct_0 @ X28)
% 12.90/13.13          | ~ (v4_orders_2 @ X28)
% 12.90/13.13          | ~ (v7_waybel_0 @ X28)
% 12.90/13.13          | ~ (l1_waybel_0 @ X28 @ X29)
% 12.90/13.13          | (m2_yellow_6 @ (sk_D_1 @ X30 @ X28 @ X29) @ X29 @ X28)
% 12.90/13.13          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 12.90/13.13          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 12.90/13.13          | ~ (l1_pre_topc @ X29)
% 12.90/13.13          | ~ (v2_pre_topc @ X29)
% 12.90/13.13          | (v2_struct_0 @ X29))),
% 12.90/13.13      inference('cnf', [status(esa)], [t32_waybel_9])).
% 12.90/13.13  thf('42', plain,
% 12.90/13.13      ((![X0 : $i]:
% 12.90/13.13          ((v2_struct_0 @ sk_B_1)
% 12.90/13.13           | (v2_struct_0 @ sk_A)
% 12.90/13.13           | ~ (v2_pre_topc @ sk_A)
% 12.90/13.13           | ~ (l1_pre_topc @ sk_A)
% 12.90/13.13           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 12.90/13.13              sk_A @ X0)
% 12.90/13.13           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.13           | ~ (v7_waybel_0 @ X0)
% 12.90/13.13           | ~ (v4_orders_2 @ X0)
% 12.90/13.13           | (v2_struct_0 @ X0)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['40', '41'])).
% 12.90/13.13  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('45', plain,
% 12.90/13.13      ((![X0 : $i]:
% 12.90/13.13          ((v2_struct_0 @ sk_B_1)
% 12.90/13.13           | (v2_struct_0 @ sk_A)
% 12.90/13.13           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.13           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 12.90/13.13              sk_A @ X0)
% 12.90/13.13           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.13           | ~ (v7_waybel_0 @ X0)
% 12.90/13.13           | ~ (v4_orders_2 @ X0)
% 12.90/13.13           | (v2_struct_0 @ X0)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('demod', [status(thm)], ['42', '43', '44'])).
% 12.90/13.13  thf('46', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.13         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.90/13.13         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.13            sk_A @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_A)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['26', '45'])).
% 12.90/13.13  thf('47', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('split', [status(esa)], ['8'])).
% 12.90/13.13  thf('48', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('split', [status(esa)], ['6'])).
% 12.90/13.13  thf('49', plain,
% 12.90/13.13      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('split', [status(esa)], ['4'])).
% 12.90/13.13  thf('50', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.13            sk_A @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_A)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 12.90/13.13  thf('51', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_A)
% 12.90/13.13         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.13            sk_A @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('simplify', [status(thm)], ['50'])).
% 12.90/13.13  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.13  thf('53', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.13            sk_A @ sk_B_1)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('clc', [status(thm)], ['51', '52'])).
% 12.90/13.13  thf(dt_m2_yellow_6, axiom,
% 12.90/13.13    (![A:$i,B:$i]:
% 12.90/13.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 12.90/13.13         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.13         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.13       ( ![C:$i]:
% 12.90/13.13         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 12.90/13.13           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 12.90/13.13             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 12.90/13.13  thf('54', plain,
% 12.90/13.13      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.13         (~ (l1_struct_0 @ X16)
% 12.90/13.13          | (v2_struct_0 @ X16)
% 12.90/13.13          | (v2_struct_0 @ X17)
% 12.90/13.13          | ~ (v4_orders_2 @ X17)
% 12.90/13.13          | ~ (v7_waybel_0 @ X17)
% 12.90/13.13          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.13          | (v4_orders_2 @ X18)
% 12.90/13.13          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.13      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.13  thf('55', plain,
% 12.90/13.13      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.13         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.90/13.13         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.13         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_B_1)
% 12.90/13.13         | (v2_struct_0 @ sk_A)
% 12.90/13.13         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.13         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.13             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.13             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.13             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.13      inference('sup-', [status(thm)], ['53', '54'])).
% 12.90/13.13  thf('56', plain,
% 12.90/13.13      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.13      inference('split', [status(esa)], ['4'])).
% 12.90/13.13  thf('57', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.13      inference('split', [status(esa)], ['6'])).
% 12.90/13.14  thf('58', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['8'])).
% 12.90/13.14  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf(dt_l1_pre_topc, axiom,
% 12.90/13.14    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 12.90/13.14  thf('60', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 12.90/13.14  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.14      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.14  thf('62', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['55', '56', '57', '58', '61'])).
% 12.90/13.14  thf('63', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['62'])).
% 12.90/13.14  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('65', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['63', '64'])).
% 12.90/13.14  thf('66', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['51', '52'])).
% 12.90/13.14  thf('67', plain,
% 12.90/13.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.14         (~ (l1_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X17)
% 12.90/13.14          | ~ (v4_orders_2 @ X17)
% 12.90/13.14          | ~ (v7_waybel_0 @ X17)
% 12.90/13.14          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.14          | (v7_waybel_0 @ X18)
% 12.90/13.14          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.14  thf('68', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.14         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['66', '67'])).
% 12.90/13.14  thf('69', plain,
% 12.90/13.14      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.14      inference('split', [status(esa)], ['4'])).
% 12.90/13.14  thf('70', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['6'])).
% 12.90/13.14  thf('71', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['8'])).
% 12.90/13.14  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.14      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.14  thf('73', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 12.90/13.14  thf('74', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['73'])).
% 12.90/13.14  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('76', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['74', '75'])).
% 12.90/13.14  thf('77', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['51', '52'])).
% 12.90/13.14  thf('78', plain,
% 12.90/13.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.14         (~ (l1_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X17)
% 12.90/13.14          | ~ (v4_orders_2 @ X17)
% 12.90/13.14          | ~ (v7_waybel_0 @ X17)
% 12.90/13.14          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.14          | (l1_waybel_0 @ X18 @ X16)
% 12.90/13.14          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.14  thf('79', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.14         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['77', '78'])).
% 12.90/13.14  thf('80', plain,
% 12.90/13.14      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.14      inference('split', [status(esa)], ['4'])).
% 12.90/13.14  thf('81', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['6'])).
% 12.90/13.14  thf('82', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['8'])).
% 12.90/13.14  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.14      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.14  thf('84', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 12.90/13.14  thf('85', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['84'])).
% 12.90/13.14  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('87', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['85', '86'])).
% 12.90/13.14  thf(d19_yellow_6, axiom,
% 12.90/13.14    (![A:$i]:
% 12.90/13.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.14       ( ![B:$i]:
% 12.90/13.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.14             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.14           ( ( v3_yellow_6 @ B @ A ) <=>
% 12.90/13.14             ( ( k10_yellow_6 @ A @ B ) != ( k1_xboole_0 ) ) ) ) ) ))).
% 12.90/13.14  thf('88', plain,
% 12.90/13.14      (![X19 : $i, X20 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X19)
% 12.90/13.14          | ~ (v4_orders_2 @ X19)
% 12.90/13.14          | ~ (v7_waybel_0 @ X19)
% 12.90/13.14          | ~ (l1_waybel_0 @ X19 @ X20)
% 12.90/13.14          | ((k10_yellow_6 @ X20 @ X19) = (k1_xboole_0))
% 12.90/13.14          | (v3_yellow_6 @ X19 @ X20)
% 12.90/13.14          | ~ (l1_pre_topc @ X20)
% 12.90/13.14          | ~ (v2_pre_topc @ X20)
% 12.90/13.14          | (v2_struct_0 @ X20))),
% 12.90/13.14      inference('cnf', [status(esa)], [d19_yellow_6])).
% 12.90/13.14  thf('89', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | ((k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['87', '88'])).
% 12.90/13.14  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('92', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | ((k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['89', '90', '91'])).
% 12.90/13.14  thf('93', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | ((k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['76', '92'])).
% 12.90/13.14  thf('94', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | ((k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['93'])).
% 12.90/13.14  thf('95', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | ((k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['65', '94'])).
% 12.90/13.14  thf('96', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | ((k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['95'])).
% 12.90/13.14  thf('97', plain,
% 12.90/13.14      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['24', '25'])).
% 12.90/13.14  thf('98', plain,
% 12.90/13.14      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['38', '39'])).
% 12.90/13.14  thf('99', plain,
% 12.90/13.14      (![X28 : $i, X29 : $i, X30 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X28)
% 12.90/13.14          | ~ (v4_orders_2 @ X28)
% 12.90/13.14          | ~ (v7_waybel_0 @ X28)
% 12.90/13.14          | ~ (l1_waybel_0 @ X28 @ X29)
% 12.90/13.14          | (r2_hidden @ X30 @ 
% 12.90/13.14             (k10_yellow_6 @ X29 @ (sk_D_1 @ X30 @ X28 @ X29)))
% 12.90/13.14          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 12.90/13.14          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 12.90/13.14          | ~ (l1_pre_topc @ X29)
% 12.90/13.14          | ~ (v2_pre_topc @ X29)
% 12.90/13.14          | (v2_struct_0 @ X29))),
% 12.90/13.14      inference('cnf', [status(esa)], [t32_waybel_9])).
% 12.90/13.14  thf('100', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_B_1)
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14           | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.14           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.90/13.14              (k10_yellow_6 @ sk_A @ 
% 12.90/13.14               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 12.90/13.14           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.14           | ~ (v7_waybel_0 @ X0)
% 12.90/13.14           | ~ (v4_orders_2 @ X0)
% 12.90/13.14           | (v2_struct_0 @ X0)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['98', '99'])).
% 12.90/13.14  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('103', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_B_1)
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.14           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.90/13.14              (k10_yellow_6 @ sk_A @ 
% 12.90/13.14               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 12.90/13.14           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.14           | ~ (v7_waybel_0 @ X0)
% 12.90/13.14           | ~ (v4_orders_2 @ X0)
% 12.90/13.14           | (v2_struct_0 @ X0)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['100', '101', '102'])).
% 12.90/13.14  thf('104', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.14         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.14         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.90/13.14         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['97', '103'])).
% 12.90/13.14  thf('105', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['8'])).
% 12.90/13.14  thf('106', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['6'])).
% 12.90/13.14  thf('107', plain,
% 12.90/13.14      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.14      inference('split', [status(esa)], ['4'])).
% 12.90/13.14  thf('108', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 12.90/13.14  thf('109', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['108'])).
% 12.90/13.14  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('111', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ 
% 12.90/13.14             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['109', '110'])).
% 12.90/13.14  thf(t7_ordinal1, axiom,
% 12.90/13.14    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.90/13.14  thf('112', plain,
% 12.90/13.14      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 12.90/13.14      inference('cnf', [status(esa)], [t7_ordinal1])).
% 12.90/13.14  thf('113', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | ~ (r1_tarski @ 
% 12.90/13.14              (k10_yellow_6 @ sk_A @ 
% 12.90/13.14               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) @ 
% 12.90/13.14              (sk_C @ sk_B_1 @ sk_A))))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['111', '112'])).
% 12.90/13.14  thf('114', plain,
% 12.90/13.14      (((~ (r1_tarski @ k1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['96', '113'])).
% 12.90/13.14  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 12.90/13.14  thf('115', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 12.90/13.14      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.90/13.14  thf('116', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['114', '115'])).
% 12.90/13.14  thf('117', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['116'])).
% 12.90/13.14  thf('118', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['51', '52'])).
% 12.90/13.14  thf('119', plain,
% 12.90/13.14      ((![X36 : $i]:
% 12.90/13.14          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A)))
% 12.90/13.14         <= ((![X36 : $i]:
% 12.90/13.14                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 12.90/13.14                 | ~ (v3_yellow_6 @ X36 @ sk_A))))),
% 12.90/13.14      inference('split', [status(esa)], ['2'])).
% 12.90/13.14  thf('120', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | ~ (v3_yellow_6 @ 
% 12.90/13.14              (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ sk_A)))
% 12.90/13.14         <= ((![X36 : $i]:
% 12.90/13.14                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 12.90/13.14                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 12.90/13.14             ((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['118', '119'])).
% 12.90/13.14  thf('121', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= ((![X36 : $i]:
% 12.90/13.14                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 12.90/13.14                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 12.90/13.14             ((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['117', '120'])).
% 12.90/13.14  thf('122', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= ((![X36 : $i]:
% 12.90/13.14                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 12.90/13.14                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 12.90/13.14             ((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['121'])).
% 12.90/13.14  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('124', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.90/13.14         <= ((![X36 : $i]:
% 12.90/13.14                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 12.90/13.14                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 12.90/13.14             ((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['122', '123'])).
% 12.90/13.14  thf('125', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.90/13.14            sk_A @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['51', '52'])).
% 12.90/13.14  thf('126', plain,
% 12.90/13.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.14         (~ (l1_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X17)
% 12.90/13.14          | ~ (v4_orders_2 @ X17)
% 12.90/13.14          | ~ (v7_waybel_0 @ X17)
% 12.90/13.14          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.14          | ~ (v2_struct_0 @ X18)
% 12.90/13.14          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.14  thf('127', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ sk_B_1)
% 12.90/13.14         | ~ (v4_orders_2 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('sup-', [status(thm)], ['125', '126'])).
% 12.90/13.14  thf('128', plain,
% 12.90/13.14      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.90/13.14      inference('split', [status(esa)], ['4'])).
% 12.90/13.14  thf('129', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['6'])).
% 12.90/13.14  thf('130', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['8'])).
% 12.90/13.14  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.14      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.14  thf('132', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 12.90/13.14  thf('133', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_B_1)))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('simplify', [status(thm)], ['132'])).
% 12.90/13.14  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('135', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_B_1)
% 12.90/13.14         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.90/13.14         <= (((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['133', '134'])).
% 12.90/13.14  thf('136', plain,
% 12.90/13.14      (((v2_struct_0 @ sk_B_1))
% 12.90/13.14         <= ((![X36 : $i]:
% 12.90/13.14                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 12.90/13.14                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 12.90/13.14             ((v1_compts_1 @ sk_A)) & 
% 12.90/13.14             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.90/13.14             ((v7_waybel_0 @ sk_B_1)) & 
% 12.90/13.14             ((v4_orders_2 @ sk_B_1)))),
% 12.90/13.14      inference('clc', [status(thm)], ['124', '135'])).
% 12.90/13.14  thf('137', plain,
% 12.90/13.14      ((~ (v2_struct_0 @ sk_B_1)) <= (~ ((v2_struct_0 @ sk_B_1)))),
% 12.90/13.14      inference('split', [status(esa)], ['10'])).
% 12.90/13.14  thf('138', plain,
% 12.90/13.14      (~ ((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A)) | 
% 12.90/13.14       ~
% 12.90/13.14       (![X36 : $i]:
% 12.90/13.14          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 12.90/13.14       ~ ((v7_waybel_0 @ sk_B_1)) | ~ ((v4_orders_2 @ sk_B_1)) | 
% 12.90/13.14       ((v2_struct_0 @ sk_B_1))),
% 12.90/13.14      inference('sup-', [status(thm)], ['136', '137'])).
% 12.90/13.14  thf('139', plain,
% 12.90/13.14      ((![X37 : $i]:
% 12.90/13.14          ((v2_struct_0 @ X37)
% 12.90/13.14           | ~ (v4_orders_2 @ X37)
% 12.90/13.14           | ~ (v7_waybel_0 @ X37)
% 12.90/13.14           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14           | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) | 
% 12.90/13.14       ((v1_compts_1 @ sk_A))),
% 12.90/13.14      inference('split', [status(esa)], ['13'])).
% 12.90/13.14  thf(t36_yellow19, axiom,
% 12.90/13.14    (![A:$i]:
% 12.90/13.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.14       ( ( v1_compts_1 @ A ) <=>
% 12.90/13.14         ( ![B:$i]:
% 12.90/13.14           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.14               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.14             ( ~( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) ) & 
% 12.90/13.14                  ( ![C:$i]:
% 12.90/13.14                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.90/13.14                      ( ~( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ) ) ) ))).
% 12.90/13.14  thf('140', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v7_waybel_0 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('141', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v4_orders_2 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('142', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v7_waybel_0 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('143', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v4_orders_2 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('144', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('145', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v4_orders_2 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('146', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v7_waybel_0 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('147', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('148', plain,
% 12.90/13.14      ((![X37 : $i]:
% 12.90/13.14          ((v2_struct_0 @ X37)
% 12.90/13.14           | ~ (v4_orders_2 @ X37)
% 12.90/13.14           | ~ (v7_waybel_0 @ X37)
% 12.90/13.14           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14           | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('split', [status(esa)], ['0'])).
% 12.90/13.14  thf('149', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['147', '148'])).
% 12.90/13.14  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('152', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['149', '150', '151'])).
% 12.90/13.14  thf('153', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['146', '152'])).
% 12.90/13.14  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('156', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['153', '154', '155'])).
% 12.90/13.14  thf('157', plain,
% 12.90/13.14      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['156'])).
% 12.90/13.14  thf('158', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['145', '157'])).
% 12.90/13.14  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('161', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['158', '159', '160'])).
% 12.90/13.14  thf('162', plain,
% 12.90/13.14      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['161'])).
% 12.90/13.14  thf('163', plain,
% 12.90/13.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.14         (~ (l1_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X17)
% 12.90/13.14          | ~ (v4_orders_2 @ X17)
% 12.90/13.14          | ~ (v7_waybel_0 @ X17)
% 12.90/13.14          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.14          | (v7_waybel_0 @ X18)
% 12.90/13.14          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.14  thf('164', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['162', '163'])).
% 12.90/13.14  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.14      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.14  thf('166', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['164', '165'])).
% 12.90/13.14  thf('167', plain,
% 12.90/13.14      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['166'])).
% 12.90/13.14  thf('168', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['144', '167'])).
% 12.90/13.14  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('171', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['168', '169', '170'])).
% 12.90/13.14  thf('172', plain,
% 12.90/13.14      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['171'])).
% 12.90/13.14  thf('173', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['143', '172'])).
% 12.90/13.14  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('176', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['173', '174', '175'])).
% 12.90/13.14  thf('177', plain,
% 12.90/13.14      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['176'])).
% 12.90/13.14  thf('178', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['142', '177'])).
% 12.90/13.14  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('181', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['178', '179', '180'])).
% 12.90/13.14  thf('182', plain,
% 12.90/13.14      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['181'])).
% 12.90/13.14  thf('183', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v4_orders_2 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('184', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v7_waybel_0 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('185', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('186', plain,
% 12.90/13.14      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['161'])).
% 12.90/13.14  thf('187', plain,
% 12.90/13.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.14         (~ (l1_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X17)
% 12.90/13.14          | ~ (v4_orders_2 @ X17)
% 12.90/13.14          | ~ (v7_waybel_0 @ X17)
% 12.90/13.14          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.14          | (v4_orders_2 @ X18)
% 12.90/13.14          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.14  thf('188', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['186', '187'])).
% 12.90/13.14  thf('189', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.14      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.14  thf('190', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['188', '189'])).
% 12.90/13.14  thf('191', plain,
% 12.90/13.14      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['190'])).
% 12.90/13.14  thf('192', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['185', '191'])).
% 12.90/13.14  thf('193', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('195', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['192', '193', '194'])).
% 12.90/13.14  thf('196', plain,
% 12.90/13.14      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['195'])).
% 12.90/13.14  thf('197', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['184', '196'])).
% 12.90/13.14  thf('198', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('200', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['197', '198', '199'])).
% 12.90/13.14  thf('201', plain,
% 12.90/13.14      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['200'])).
% 12.90/13.14  thf('202', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['183', '201'])).
% 12.90/13.14  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('205', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['202', '203', '204'])).
% 12.90/13.14  thf('206', plain,
% 12.90/13.14      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['205'])).
% 12.90/13.14  thf('207', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v4_orders_2 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('208', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v7_waybel_0 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('209', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('210', plain,
% 12.90/13.14      ((![X37 : $i]:
% 12.90/13.14          ((v2_struct_0 @ X37)
% 12.90/13.14           | ~ (v4_orders_2 @ X37)
% 12.90/13.14           | ~ (v7_waybel_0 @ X37)
% 12.90/13.14           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14           | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('split', [status(esa)], ['13'])).
% 12.90/13.14  thf('211', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['209', '210'])).
% 12.90/13.14  thf('212', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('214', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('demod', [status(thm)], ['211', '212', '213'])).
% 12.90/13.14  thf('215', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['208', '214'])).
% 12.90/13.14  thf('216', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('218', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('demod', [status(thm)], ['215', '216', '217'])).
% 12.90/13.14  thf('219', plain,
% 12.90/13.14      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['218'])).
% 12.90/13.14  thf('220', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['207', '219'])).
% 12.90/13.14  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('223', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('demod', [status(thm)], ['220', '221', '222'])).
% 12.90/13.14  thf('224', plain,
% 12.90/13.14      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['223'])).
% 12.90/13.14  thf('225', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v7_waybel_0 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('226', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v4_orders_2 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('227', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('228', plain,
% 12.90/13.14      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['161'])).
% 12.90/13.14  thf('229', plain,
% 12.90/13.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.14         (~ (l1_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X16)
% 12.90/13.14          | (v2_struct_0 @ X17)
% 12.90/13.14          | ~ (v4_orders_2 @ X17)
% 12.90/13.14          | ~ (v7_waybel_0 @ X17)
% 12.90/13.14          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.14          | (l1_waybel_0 @ X18 @ X16)
% 12.90/13.14          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.14  thf('230', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['228', '229'])).
% 12.90/13.14  thf('231', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.14      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.14  thf('232', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['230', '231'])).
% 12.90/13.14  thf('233', plain,
% 12.90/13.14      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['232'])).
% 12.90/13.14  thf('234', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['227', '233'])).
% 12.90/13.14  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('237', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['234', '235', '236'])).
% 12.90/13.14  thf('238', plain,
% 12.90/13.14      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['237'])).
% 12.90/13.14  thf('239', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['226', '238'])).
% 12.90/13.14  thf('240', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('242', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['239', '240', '241'])).
% 12.90/13.14  thf('243', plain,
% 12.90/13.14      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['242'])).
% 12.90/13.14  thf('244', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['225', '243'])).
% 12.90/13.14  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('247', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['244', '245', '246'])).
% 12.90/13.14  thf('248', plain,
% 12.90/13.14      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['247'])).
% 12.90/13.14  thf('249', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v7_waybel_0 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('250', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((v4_orders_2 @ (sk_B @ X33))
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('251', plain,
% 12.90/13.14      (![X33 : $i]:
% 12.90/13.14         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 12.90/13.14          | (v1_compts_1 @ X33)
% 12.90/13.14          | ~ (l1_pre_topc @ X33)
% 12.90/13.14          | ~ (v2_pre_topc @ X33)
% 12.90/13.14          | (v2_struct_0 @ X33))),
% 12.90/13.14      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.14  thf('252', plain,
% 12.90/13.14      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['161'])).
% 12.90/13.14  thf('253', plain,
% 12.90/13.14      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['181'])).
% 12.90/13.14  thf('254', plain,
% 12.90/13.14      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['205'])).
% 12.90/13.14  thf('255', plain,
% 12.90/13.14      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['247'])).
% 12.90/13.14  thf('256', plain,
% 12.90/13.14      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['205'])).
% 12.90/13.14  thf('257', plain,
% 12.90/13.14      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['181'])).
% 12.90/13.14  thf('258', plain,
% 12.90/13.14      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['247'])).
% 12.90/13.14  thf(t4_subset_1, axiom,
% 12.90/13.14    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 12.90/13.14  thf('259', plain,
% 12.90/13.14      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 12.90/13.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.90/13.14  thf(d18_yellow_6, axiom,
% 12.90/13.14    (![A:$i]:
% 12.90/13.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.14       ( ![B:$i]:
% 12.90/13.14         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.14             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.14           ( ![C:$i]:
% 12.90/13.14             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.14               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 12.90/13.14                 ( ![D:$i]:
% 12.90/13.14                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 12.90/13.14                     ( ( r2_hidden @ D @ C ) <=>
% 12.90/13.14                       ( ![E:$i]:
% 12.90/13.14                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 12.90/13.14                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.90/13.14  thf('260', plain,
% 12.90/13.14      (![X8 : $i, X9 : $i, X10 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X8)
% 12.90/13.14          | ~ (v4_orders_2 @ X8)
% 12.90/13.14          | ~ (v7_waybel_0 @ X8)
% 12.90/13.14          | ~ (l1_waybel_0 @ X8 @ X9)
% 12.90/13.14          | (m1_subset_1 @ (sk_D @ X10 @ X8 @ X9) @ (u1_struct_0 @ X9))
% 12.90/13.14          | ((X10) = (k10_yellow_6 @ X9 @ X8))
% 12.90/13.14          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 12.90/13.14          | ~ (l1_pre_topc @ X9)
% 12.90/13.14          | ~ (v2_pre_topc @ X9)
% 12.90/13.14          | (v2_struct_0 @ X9))),
% 12.90/13.14      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.90/13.14  thf('261', plain,
% 12.90/13.14      (![X0 : $i, X1 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X0)
% 12.90/13.14          | ~ (v2_pre_topc @ X0)
% 12.90/13.14          | ~ (l1_pre_topc @ X0)
% 12.90/13.14          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 12.90/13.14          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ (u1_struct_0 @ X0))
% 12.90/13.14          | ~ (l1_waybel_0 @ X1 @ X0)
% 12.90/13.14          | ~ (v7_waybel_0 @ X1)
% 12.90/13.14          | ~ (v4_orders_2 @ X1)
% 12.90/13.14          | (v2_struct_0 @ X1))),
% 12.90/13.14      inference('sup-', [status(thm)], ['259', '260'])).
% 12.90/13.14  thf('262', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['258', '261'])).
% 12.90/13.14  thf('263', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('264', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('265', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['262', '263', '264'])).
% 12.90/13.14  thf('266', plain,
% 12.90/13.14      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['265'])).
% 12.90/13.14  thf('267', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['257', '266'])).
% 12.90/13.14  thf('268', plain,
% 12.90/13.14      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['267'])).
% 12.90/13.14  thf('269', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['256', '268'])).
% 12.90/13.14  thf('270', plain,
% 12.90/13.14      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['269'])).
% 12.90/13.14  thf('271', plain,
% 12.90/13.14      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['269'])).
% 12.90/13.14  thf('272', plain,
% 12.90/13.14      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['205'])).
% 12.90/13.14  thf('273', plain,
% 12.90/13.14      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['181'])).
% 12.90/13.14  thf('274', plain,
% 12.90/13.14      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['247'])).
% 12.90/13.14  thf('275', plain,
% 12.90/13.14      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (m1_subset_1 @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (u1_struct_0 @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['269'])).
% 12.90/13.14  thf('276', plain,
% 12.90/13.14      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['205'])).
% 12.90/13.14  thf('277', plain,
% 12.90/13.14      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['181'])).
% 12.90/13.14  thf('278', plain,
% 12.90/13.14      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['247'])).
% 12.90/13.14  thf('279', plain,
% 12.90/13.14      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['181'])).
% 12.90/13.14  thf('280', plain,
% 12.90/13.14      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['205'])).
% 12.90/13.14  thf('281', plain,
% 12.90/13.14      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['247'])).
% 12.90/13.14  thf(dt_k10_yellow_6, axiom,
% 12.90/13.14    (![A:$i,B:$i]:
% 12.90/13.14     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 12.90/13.14         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 12.90/13.14         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.14       ( m1_subset_1 @
% 12.90/13.14         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 12.90/13.14  thf('282', plain,
% 12.90/13.14      (![X14 : $i, X15 : $i]:
% 12.90/13.14         (~ (l1_pre_topc @ X14)
% 12.90/13.14          | ~ (v2_pre_topc @ X14)
% 12.90/13.14          | (v2_struct_0 @ X14)
% 12.90/13.14          | (v2_struct_0 @ X15)
% 12.90/13.14          | ~ (v4_orders_2 @ X15)
% 12.90/13.14          | ~ (v7_waybel_0 @ X15)
% 12.90/13.14          | ~ (l1_waybel_0 @ X15 @ X14)
% 12.90/13.14          | (m1_subset_1 @ (k10_yellow_6 @ X14 @ X15) @ 
% 12.90/13.14             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 12.90/13.14      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 12.90/13.14  thf('283', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['281', '282'])).
% 12.90/13.14  thf('284', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('285', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('286', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['283', '284', '285'])).
% 12.90/13.14  thf('287', plain,
% 12.90/13.14      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['286'])).
% 12.90/13.14  thf('288', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['280', '287'])).
% 12.90/13.14  thf('289', plain,
% 12.90/13.14      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['288'])).
% 12.90/13.14  thf('290', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['279', '289'])).
% 12.90/13.14  thf('291', plain,
% 12.90/13.14      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['290'])).
% 12.90/13.14  thf('292', plain,
% 12.90/13.14      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X8)
% 12.90/13.14          | ~ (v4_orders_2 @ X8)
% 12.90/13.14          | ~ (v7_waybel_0 @ X8)
% 12.90/13.14          | ~ (l1_waybel_0 @ X8 @ X9)
% 12.90/13.14          | ((X10) != (k10_yellow_6 @ X9 @ X8))
% 12.90/13.14          | (r2_hidden @ X12 @ X10)
% 12.90/13.14          | (m1_connsp_2 @ (sk_E_1 @ X12 @ X8 @ X9) @ X9 @ X12)
% 12.90/13.14          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 12.90/13.14          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 12.90/13.14          | ~ (l1_pre_topc @ X9)
% 12.90/13.14          | ~ (v2_pre_topc @ X9)
% 12.90/13.14          | (v2_struct_0 @ X9))),
% 12.90/13.14      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.90/13.14  thf('293', plain,
% 12.90/13.14      (![X8 : $i, X9 : $i, X12 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X9)
% 12.90/13.14          | ~ (v2_pre_topc @ X9)
% 12.90/13.14          | ~ (l1_pre_topc @ X9)
% 12.90/13.14          | ~ (m1_subset_1 @ (k10_yellow_6 @ X9 @ X8) @ 
% 12.90/13.14               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 12.90/13.14          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 12.90/13.14          | (m1_connsp_2 @ (sk_E_1 @ X12 @ X8 @ X9) @ X9 @ X12)
% 12.90/13.14          | (r2_hidden @ X12 @ (k10_yellow_6 @ X9 @ X8))
% 12.90/13.14          | ~ (l1_waybel_0 @ X8 @ X9)
% 12.90/13.14          | ~ (v7_waybel_0 @ X8)
% 12.90/13.14          | ~ (v4_orders_2 @ X8)
% 12.90/13.14          | (v2_struct_0 @ X8))),
% 12.90/13.14      inference('simplify', [status(thm)], ['292'])).
% 12.90/13.14  thf('294', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14           | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['291', '293'])).
% 12.90/13.14  thf('295', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('296', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('297', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['294', '295', '296'])).
% 12.90/13.14  thf('298', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['297'])).
% 12.90/13.14  thf('299', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['278', '298'])).
% 12.90/13.14  thf('300', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['299'])).
% 12.90/13.14  thf('301', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['277', '300'])).
% 12.90/13.14  thf('302', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['301'])).
% 12.90/13.14  thf('303', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['276', '302'])).
% 12.90/13.14  thf('304', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14              sk_A @ X0)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['303'])).
% 12.90/13.14  thf('305', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (m1_connsp_2 @ 
% 12.90/13.14            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['275', '304'])).
% 12.90/13.14  thf('306', plain,
% 12.90/13.14      ((((m1_connsp_2 @ 
% 12.90/13.14          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14          sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['305'])).
% 12.90/13.14  thf('307', plain,
% 12.90/13.14      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 12.90/13.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.90/13.14  thf('308', plain,
% 12.90/13.14      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X8)
% 12.90/13.14          | ~ (v4_orders_2 @ X8)
% 12.90/13.14          | ~ (v7_waybel_0 @ X8)
% 12.90/13.14          | ~ (l1_waybel_0 @ X8 @ X9)
% 12.90/13.14          | (r2_hidden @ (sk_D @ X10 @ X8 @ X9) @ X10)
% 12.90/13.14          | (r1_waybel_0 @ X9 @ X8 @ X11)
% 12.90/13.14          | ~ (m1_connsp_2 @ X11 @ X9 @ (sk_D @ X10 @ X8 @ X9))
% 12.90/13.14          | ((X10) = (k10_yellow_6 @ X9 @ X8))
% 12.90/13.14          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 12.90/13.14          | ~ (l1_pre_topc @ X9)
% 12.90/13.14          | ~ (v2_pre_topc @ X9)
% 12.90/13.14          | (v2_struct_0 @ X9))),
% 12.90/13.14      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.90/13.14  thf('309', plain,
% 12.90/13.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X0)
% 12.90/13.14          | ~ (v2_pre_topc @ X0)
% 12.90/13.14          | ~ (l1_pre_topc @ X0)
% 12.90/13.14          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 12.90/13.14          | ~ (m1_connsp_2 @ X2 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0))
% 12.90/13.14          | (r1_waybel_0 @ X0 @ X1 @ X2)
% 12.90/13.14          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 12.90/13.14          | ~ (l1_waybel_0 @ X1 @ X0)
% 12.90/13.14          | ~ (v7_waybel_0 @ X1)
% 12.90/13.14          | ~ (v4_orders_2 @ X1)
% 12.90/13.14          | (v2_struct_0 @ X1))),
% 12.90/13.14      inference('sup-', [status(thm)], ['307', '308'])).
% 12.90/13.14  thf('310', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['306', '309'])).
% 12.90/13.14  thf('311', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('312', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('313', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['310', '311', '312'])).
% 12.90/13.14  thf('314', plain,
% 12.90/13.14      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['313'])).
% 12.90/13.14  thf('315', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['274', '314'])).
% 12.90/13.14  thf('316', plain,
% 12.90/13.14      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['315'])).
% 12.90/13.14  thf('317', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['273', '316'])).
% 12.90/13.14  thf('318', plain,
% 12.90/13.14      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['317'])).
% 12.90/13.14  thf('319', plain,
% 12.90/13.14      ((((v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ sk_A)
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['272', '318'])).
% 12.90/13.14  thf('320', plain,
% 12.90/13.14      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            k1_xboole_0)
% 12.90/13.14         | (r2_hidden @ 
% 12.90/13.14            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.14            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['319'])).
% 12.90/13.14  thf('321', plain,
% 12.90/13.14      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['205'])).
% 12.90/13.14  thf('322', plain,
% 12.90/13.14      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['181'])).
% 12.90/13.14  thf('323', plain,
% 12.90/13.14      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['247'])).
% 12.90/13.14  thf('324', plain,
% 12.90/13.14      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.90/13.14            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.14         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14         | (v1_compts_1 @ sk_A)
% 12.90/13.14         | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['290'])).
% 12.90/13.14  thf('325', plain,
% 12.90/13.14      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X8)
% 12.90/13.14          | ~ (v4_orders_2 @ X8)
% 12.90/13.14          | ~ (v7_waybel_0 @ X8)
% 12.90/13.14          | ~ (l1_waybel_0 @ X8 @ X9)
% 12.90/13.14          | ((X10) != (k10_yellow_6 @ X9 @ X8))
% 12.90/13.14          | (r2_hidden @ X12 @ X10)
% 12.90/13.14          | ~ (r1_waybel_0 @ X9 @ X8 @ (sk_E_1 @ X12 @ X8 @ X9))
% 12.90/13.14          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 12.90/13.14          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 12.90/13.14          | ~ (l1_pre_topc @ X9)
% 12.90/13.14          | ~ (v2_pre_topc @ X9)
% 12.90/13.14          | (v2_struct_0 @ X9))),
% 12.90/13.14      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.90/13.14  thf('326', plain,
% 12.90/13.14      (![X8 : $i, X9 : $i, X12 : $i]:
% 12.90/13.14         ((v2_struct_0 @ X9)
% 12.90/13.14          | ~ (v2_pre_topc @ X9)
% 12.90/13.14          | ~ (l1_pre_topc @ X9)
% 12.90/13.14          | ~ (m1_subset_1 @ (k10_yellow_6 @ X9 @ X8) @ 
% 12.90/13.14               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 12.90/13.14          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X9))
% 12.90/13.14          | ~ (r1_waybel_0 @ X9 @ X8 @ (sk_E_1 @ X12 @ X8 @ X9))
% 12.90/13.14          | (r2_hidden @ X12 @ (k10_yellow_6 @ X9 @ X8))
% 12.90/13.14          | ~ (l1_waybel_0 @ X8 @ X9)
% 12.90/13.14          | ~ (v7_waybel_0 @ X8)
% 12.90/13.14          | ~ (v4_orders_2 @ X8)
% 12.90/13.14          | (v2_struct_0 @ X8))),
% 12.90/13.14      inference('simplify', [status(thm)], ['325'])).
% 12.90/13.14  thf('327', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | ~ (l1_pre_topc @ sk_A)
% 12.90/13.14           | ~ (v2_pre_topc @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['324', '326'])).
% 12.90/13.14  thf('328', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('329', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.14  thf('330', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('demod', [status(thm)], ['327', '328', '329'])).
% 12.90/13.14  thf('331', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['330'])).
% 12.90/13.14  thf('332', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['323', '331'])).
% 12.90/13.14  thf('333', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['332'])).
% 12.90/13.14  thf('334', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['322', '333'])).
% 12.90/13.14  thf('335', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('simplify', [status(thm)], ['334'])).
% 12.90/13.14  thf('336', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          ((v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ sk_A)
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.14                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.14                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.14      inference('sup-', [status(thm)], ['321', '335'])).
% 12.90/13.14  thf('337', plain,
% 12.90/13.14      ((![X0 : $i]:
% 12.90/13.14          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.90/13.14           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.14                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.14           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.14           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.14           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.14           | (v1_compts_1 @ sk_A)
% 12.90/13.14           | (v2_struct_0 @ sk_A)))
% 12.90/13.14         <= ((![X37 : $i]:
% 12.90/13.14                ((v2_struct_0 @ X37)
% 12.90/13.14                 | ~ (v4_orders_2 @ X37)
% 12.90/13.14                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['336'])).
% 12.90/13.15  thf('338', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | ~ (m1_subset_1 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15              (u1_struct_0 @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['320', '337'])).
% 12.90/13.15  thf('339', plain,
% 12.90/13.15      (((~ (m1_subset_1 @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (u1_struct_0 @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['338'])).
% 12.90/13.15  thf('340', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['271', '339'])).
% 12.90/13.15  thf('341', plain,
% 12.90/13.15      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15          k1_xboole_0)
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['340'])).
% 12.90/13.15  thf(t29_waybel_9, axiom,
% 12.90/13.15    (![A:$i]:
% 12.90/13.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.15       ( ![B:$i]:
% 12.90/13.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.15             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.15           ( ![C:$i]:
% 12.90/13.15             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.90/13.15               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) =>
% 12.90/13.15                 ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 12.90/13.15  thf('342', plain,
% 12.90/13.15      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.90/13.15         ((v2_struct_0 @ X21)
% 12.90/13.15          | ~ (v4_orders_2 @ X21)
% 12.90/13.15          | ~ (v7_waybel_0 @ X21)
% 12.90/13.15          | ~ (l1_waybel_0 @ X21 @ X22)
% 12.90/13.15          | ~ (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 12.90/13.15          | (r3_waybel_9 @ X22 @ X21 @ X23)
% 12.90/13.15          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 12.90/13.15          | ~ (l1_pre_topc @ X22)
% 12.90/13.15          | ~ (v2_pre_topc @ X22)
% 12.90/13.15          | (v2_struct_0 @ X22))),
% 12.90/13.15      inference('cnf', [status(esa)], [t29_waybel_9])).
% 12.90/13.15  thf('343', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | ~ (m1_subset_1 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15              (u1_struct_0 @ sk_A))
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['341', '342'])).
% 12.90/13.15  thf('344', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('345', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('346', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (m1_subset_1 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15              (u1_struct_0 @ sk_A))
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['343', '344', '345'])).
% 12.90/13.15  thf('347', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (m1_subset_1 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15              (u1_struct_0 @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['346'])).
% 12.90/13.15  thf('348', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['270', '347'])).
% 12.90/13.15  thf('349', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['348'])).
% 12.90/13.15  thf('350', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['255', '349'])).
% 12.90/13.15  thf('351', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['350'])).
% 12.90/13.15  thf('352', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['254', '351'])).
% 12.90/13.15  thf('353', plain,
% 12.90/13.15      (((~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['352'])).
% 12.90/13.15  thf('354', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['253', '353'])).
% 12.90/13.15  thf('355', plain,
% 12.90/13.15      ((((r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.90/13.15          (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['354'])).
% 12.90/13.15  thf('356', plain,
% 12.90/13.15      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (m1_subset_1 @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (u1_struct_0 @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['269'])).
% 12.90/13.15  thf(t31_waybel_9, axiom,
% 12.90/13.15    (![A:$i]:
% 12.90/13.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.15       ( ![B:$i]:
% 12.90/13.15         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.90/13.15             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.90/13.15           ( ![C:$i]:
% 12.90/13.15             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 12.90/13.15               ( ![D:$i]:
% 12.90/13.15                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 12.90/13.15                   ( ( r3_waybel_9 @ A @ C @ D ) => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 12.90/13.15  thf('357', plain,
% 12.90/13.15      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 12.90/13.15         ((v2_struct_0 @ X24)
% 12.90/13.15          | ~ (v4_orders_2 @ X24)
% 12.90/13.15          | ~ (v7_waybel_0 @ X24)
% 12.90/13.15          | ~ (l1_waybel_0 @ X24 @ X25)
% 12.90/13.15          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 12.90/13.15          | (r3_waybel_9 @ X25 @ X24 @ X26)
% 12.90/13.15          | ~ (r3_waybel_9 @ X25 @ X27 @ X26)
% 12.90/13.15          | ~ (m2_yellow_6 @ X27 @ X25 @ X24)
% 12.90/13.15          | ~ (l1_pre_topc @ X25)
% 12.90/13.15          | ~ (v2_pre_topc @ X25)
% 12.90/13.15          | (v2_struct_0 @ X25))),
% 12.90/13.15      inference('cnf', [status(esa)], [t31_waybel_9])).
% 12.90/13.15  thf('358', plain,
% 12.90/13.15      ((![X0 : $i, X1 : $i]:
% 12.90/13.15          ((v2_struct_0 @ sk_A)
% 12.90/13.15           | (v1_compts_1 @ sk_A)
% 12.90/13.15           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15           | (v2_struct_0 @ sk_A)
% 12.90/13.15           | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15           | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 12.90/13.15           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 12.90/13.15                (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.15           | ~ (v7_waybel_0 @ X0)
% 12.90/13.15           | ~ (v4_orders_2 @ X0)
% 12.90/13.15           | (v2_struct_0 @ X0)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['356', '357'])).
% 12.90/13.15  thf('359', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('360', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('361', plain,
% 12.90/13.15      ((![X0 : $i, X1 : $i]:
% 12.90/13.15          ((v2_struct_0 @ sk_A)
% 12.90/13.15           | (v1_compts_1 @ sk_A)
% 12.90/13.15           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15           | (v2_struct_0 @ sk_A)
% 12.90/13.15           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 12.90/13.15           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 12.90/13.15                (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.15           | ~ (v7_waybel_0 @ X0)
% 12.90/13.15           | ~ (v4_orders_2 @ X0)
% 12.90/13.15           | (v2_struct_0 @ X0)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['358', '359', '360'])).
% 12.90/13.15  thf('362', plain,
% 12.90/13.15      ((![X0 : $i, X1 : $i]:
% 12.90/13.15          ((v2_struct_0 @ X0)
% 12.90/13.15           | ~ (v4_orders_2 @ X0)
% 12.90/13.15           | ~ (v7_waybel_0 @ X0)
% 12.90/13.15           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.15           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 12.90/13.15                (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 12.90/13.15           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15           | (v1_compts_1 @ sk_A)
% 12.90/13.15           | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['361'])).
% 12.90/13.15  thf('363', plain,
% 12.90/13.15      ((![X0 : $i]:
% 12.90/13.15          ((v2_struct_0 @ sk_A)
% 12.90/13.15           | (v1_compts_1 @ sk_A)
% 12.90/13.15           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15           | (r2_hidden @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15              k1_xboole_0)
% 12.90/13.15           | (v2_struct_0 @ sk_A)
% 12.90/13.15           | (v1_compts_1 @ sk_A)
% 12.90/13.15           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 12.90/13.15           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.15           | ~ (v7_waybel_0 @ X0)
% 12.90/13.15           | ~ (v4_orders_2 @ X0)
% 12.90/13.15           | (v2_struct_0 @ X0)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['355', '362'])).
% 12.90/13.15  thf('364', plain,
% 12.90/13.15      ((![X0 : $i]:
% 12.90/13.15          ((v2_struct_0 @ X0)
% 12.90/13.15           | ~ (v4_orders_2 @ X0)
% 12.90/13.15           | ~ (v7_waybel_0 @ X0)
% 12.90/13.15           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.90/13.15           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 12.90/13.15           | (r2_hidden @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15              k1_xboole_0)
% 12.90/13.15           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15           | (v1_compts_1 @ sk_A)
% 12.90/13.15           | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['363'])).
% 12.90/13.15  thf('365', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['252', '364'])).
% 12.90/13.15  thf('366', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['365'])).
% 12.90/13.15  thf('367', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['251', '366'])).
% 12.90/13.15  thf('368', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('369', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('370', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['367', '368', '369'])).
% 12.90/13.15  thf('371', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['370'])).
% 12.90/13.15  thf('372', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['250', '371'])).
% 12.90/13.15  thf('373', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('374', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('375', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['372', '373', '374'])).
% 12.90/13.15  thf('376', plain,
% 12.90/13.15      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['375'])).
% 12.90/13.15  thf('377', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['249', '376'])).
% 12.90/13.15  thf('378', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('379', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('380', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['377', '378', '379'])).
% 12.90/13.15  thf('381', plain,
% 12.90/13.15      ((((r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15          (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['380'])).
% 12.90/13.15  thf('382', plain,
% 12.90/13.15      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (m1_subset_1 @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            (u1_struct_0 @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['269'])).
% 12.90/13.15  thf('383', plain,
% 12.90/13.15      (![X33 : $i, X34 : $i]:
% 12.90/13.15         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 12.90/13.15          | ~ (r3_waybel_9 @ X33 @ (sk_B @ X33) @ X34)
% 12.90/13.15          | (v1_compts_1 @ X33)
% 12.90/13.15          | ~ (l1_pre_topc @ X33)
% 12.90/13.15          | ~ (v2_pre_topc @ X33)
% 12.90/13.15          | (v2_struct_0 @ X33))),
% 12.90/13.15      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.15  thf('384', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['382', '383'])).
% 12.90/13.15  thf('385', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('386', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('387', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['384', '385', '386'])).
% 12.90/13.15  thf('388', plain,
% 12.90/13.15      (((~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['387'])).
% 12.90/13.15  thf('389', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (r2_hidden @ 
% 12.90/13.15            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15            k1_xboole_0)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['381', '388'])).
% 12.90/13.15  thf('390', plain,
% 12.90/13.15      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.90/13.15          k1_xboole_0)
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['389'])).
% 12.90/13.15  thf('391', plain,
% 12.90/13.15      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (r1_tarski @ X6 @ X5))),
% 12.90/13.15      inference('cnf', [status(esa)], [t7_ordinal1])).
% 12.90/13.15  thf('392', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.90/13.15         | ~ (r1_tarski @ k1_xboole_0 @ 
% 12.90/13.15              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['390', '391'])).
% 12.90/13.15  thf('393', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 12.90/13.15      inference('cnf', [status(esa)], [t2_xboole_1])).
% 12.90/13.15  thf('394', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['392', '393'])).
% 12.90/13.15  thf('395', plain,
% 12.90/13.15      (![X19 : $i, X20 : $i]:
% 12.90/13.15         ((v2_struct_0 @ X19)
% 12.90/13.15          | ~ (v4_orders_2 @ X19)
% 12.90/13.15          | ~ (v7_waybel_0 @ X19)
% 12.90/13.15          | ~ (l1_waybel_0 @ X19 @ X20)
% 12.90/13.15          | ~ (v3_yellow_6 @ X19 @ X20)
% 12.90/13.15          | ((k10_yellow_6 @ X20 @ X19) != (k1_xboole_0))
% 12.90/13.15          | ~ (l1_pre_topc @ X20)
% 12.90/13.15          | ~ (v2_pre_topc @ X20)
% 12.90/13.15          | (v2_struct_0 @ X20))),
% 12.90/13.15      inference('cnf', [status(esa)], [d19_yellow_6])).
% 12.90/13.15  thf('396', plain,
% 12.90/13.15      (((((k1_xboole_0) != (k1_xboole_0))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['394', '395'])).
% 12.90/13.15  thf('397', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('398', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('399', plain,
% 12.90/13.15      (((((k1_xboole_0) != (k1_xboole_0))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['396', '397', '398'])).
% 12.90/13.15  thf('400', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['399'])).
% 12.90/13.15  thf('401', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['248', '400'])).
% 12.90/13.15  thf('402', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['401'])).
% 12.90/13.15  thf('403', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['224', '402'])).
% 12.90/13.15  thf('404', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['403'])).
% 12.90/13.15  thf('405', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['206', '404'])).
% 12.90/13.15  thf('406', plain,
% 12.90/13.15      (((~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['405'])).
% 12.90/13.15  thf('407', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['182', '406'])).
% 12.90/13.15  thf('408', plain,
% 12.90/13.15      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['407'])).
% 12.90/13.15  thf('409', plain,
% 12.90/13.15      (![X33 : $i]:
% 12.90/13.15         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 12.90/13.15          | (v1_compts_1 @ X33)
% 12.90/13.15          | ~ (l1_pre_topc @ X33)
% 12.90/13.15          | ~ (v2_pre_topc @ X33)
% 12.90/13.15          | (v2_struct_0 @ X33))),
% 12.90/13.15      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.15  thf('410', plain,
% 12.90/13.15      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['161'])).
% 12.90/13.15  thf('411', plain,
% 12.90/13.15      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.15         (~ (l1_struct_0 @ X16)
% 12.90/13.15          | (v2_struct_0 @ X16)
% 12.90/13.15          | (v2_struct_0 @ X17)
% 12.90/13.15          | ~ (v4_orders_2 @ X17)
% 12.90/13.15          | ~ (v7_waybel_0 @ X17)
% 12.90/13.15          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.90/13.15          | ~ (v2_struct_0 @ X18)
% 12.90/13.15          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 12.90/13.15      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.90/13.15  thf('412', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (l1_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['410', '411'])).
% 12.90/13.15  thf('413', plain, ((l1_struct_0 @ sk_A)),
% 12.90/13.15      inference('sup-', [status(thm)], ['59', '60'])).
% 12.90/13.15  thf('414', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['412', '413'])).
% 12.90/13.15  thf('415', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.90/13.15         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['414'])).
% 12.90/13.15  thf('416', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['409', '415'])).
% 12.90/13.15  thf('417', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('418', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('419', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['416', '417', '418'])).
% 12.90/13.15  thf('420', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['419'])).
% 12.90/13.15  thf('421', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['408', '420'])).
% 12.90/13.15  thf('422', plain,
% 12.90/13.15      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['421'])).
% 12.90/13.15  thf('423', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['141', '422'])).
% 12.90/13.15  thf('424', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('425', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('426', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['423', '424', '425'])).
% 12.90/13.15  thf('427', plain,
% 12.90/13.15      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['426'])).
% 12.90/13.15  thf('428', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['140', '427'])).
% 12.90/13.15  thf('429', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('430', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('431', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['428', '429', '430'])).
% 12.90/13.15  thf('432', plain,
% 12.90/13.15      ((((v2_struct_0 @ (sk_B @ sk_A))
% 12.90/13.15         | (v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['431'])).
% 12.90/13.15  thf('433', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('434', plain,
% 12.90/13.15      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('clc', [status(thm)], ['432', '433'])).
% 12.90/13.15  thf('435', plain,
% 12.90/13.15      (![X33 : $i]:
% 12.90/13.15         (~ (v2_struct_0 @ (sk_B @ X33))
% 12.90/13.15          | (v1_compts_1 @ X33)
% 12.90/13.15          | ~ (l1_pre_topc @ X33)
% 12.90/13.15          | ~ (v2_pre_topc @ X33)
% 12.90/13.15          | (v2_struct_0 @ X33))),
% 12.90/13.15      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.90/13.15  thf('436', plain,
% 12.90/13.15      ((((v1_compts_1 @ sk_A)
% 12.90/13.15         | (v2_struct_0 @ sk_A)
% 12.90/13.15         | ~ (v2_pre_topc @ sk_A)
% 12.90/13.15         | ~ (l1_pre_topc @ sk_A)
% 12.90/13.15         | (v1_compts_1 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('sup-', [status(thm)], ['434', '435'])).
% 12.90/13.15  thf('437', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('438', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('439', plain,
% 12.90/13.15      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('demod', [status(thm)], ['436', '437', '438'])).
% 12.90/13.15  thf('440', plain,
% 12.90/13.15      ((((v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('simplify', [status(thm)], ['439'])).
% 12.90/13.15  thf('441', plain, (~ (v2_struct_0 @ sk_A)),
% 12.90/13.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.15  thf('442', plain,
% 12.90/13.15      (((v1_compts_1 @ sk_A))
% 12.90/13.15         <= ((![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 12.90/13.15             (![X37 : $i]:
% 12.90/13.15                ((v2_struct_0 @ X37)
% 12.90/13.15                 | ~ (v4_orders_2 @ X37)
% 12.90/13.15                 | ~ (v7_waybel_0 @ X37)
% 12.90/13.15                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 12.90/13.15      inference('clc', [status(thm)], ['440', '441'])).
% 12.90/13.15  thf('443', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 12.90/13.15      inference('split', [status(esa)], ['2'])).
% 12.90/13.15  thf('444', plain,
% 12.90/13.15      (~
% 12.90/13.15       (![X37 : $i]:
% 12.90/13.15          ((v2_struct_0 @ X37)
% 12.90/13.15           | ~ (v4_orders_2 @ X37)
% 12.90/13.15           | ~ (v7_waybel_0 @ X37)
% 12.90/13.15           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15           | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) | 
% 12.90/13.15       ((v1_compts_1 @ sk_A)) | 
% 12.90/13.15       ~
% 12.90/13.15       (![X37 : $i]:
% 12.90/13.15          ((v2_struct_0 @ X37)
% 12.90/13.15           | ~ (v4_orders_2 @ X37)
% 12.90/13.15           | ~ (v7_waybel_0 @ X37)
% 12.90/13.15           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 12.90/13.15           | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37)))),
% 12.90/13.15      inference('sup-', [status(thm)], ['442', '443'])).
% 12.90/13.15  thf('445', plain, ($false),
% 12.90/13.15      inference('sat_resolution*', [status(thm)],
% 12.90/13.15                ['1', '3', '5', '7', '9', '11', '138', '139', '444'])).
% 12.90/13.15  
% 12.90/13.15  % SZS output end Refutation
% 12.90/13.15  
% 12.90/13.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
