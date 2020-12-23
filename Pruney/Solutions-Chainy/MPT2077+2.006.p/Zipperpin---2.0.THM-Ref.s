%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sVbZp7for3

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:58 EST 2020

% Result     : Theorem 4.25s
% Output     : Refutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  424 (2579 expanded)
%              Number of leaves         :   41 ( 694 expanded)
%              Depth                    :   84
%              Number of atoms          : 8817 (53505 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(k6_yellow_6_type,type,(
    k6_yellow_6: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
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
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
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

thf('257',plain,
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

thf('259',plain,(
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

thf('260',plain,
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
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
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
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
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
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,
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
    inference('sup-',[status(thm)],['257','264'])).

thf('266',plain,
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
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,
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
    inference('sup-',[status(thm)],['256','266'])).

thf('268',plain,
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
    inference(simplify,[status(thm)],['267'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('269',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('270',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['268','271'])).

thf('273',plain,
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
    inference(simplify,[status(thm)],['267'])).

thf('274',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('275',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ X7 @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['273','276'])).

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

thf('278',plain,(
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

thf('279',plain,
    ( ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
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
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
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
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['282'])).

thf('284',plain,
    ( ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['272','283'])).

thf('285',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['255','285'])).

thf('287',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
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
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['254','287'])).

thf('289',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
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
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['253','289'])).

thf('291',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
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

thf('292',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['268','271'])).

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

thf('293',plain,(
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

thf('294',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
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
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
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
    inference(demod,[status(thm)],['294','295','296'])).

thf('298',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 ) )
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
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
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
    inference('sup-',[status(thm)],['291','298'])).

thf('300',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
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
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
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
    inference('sup-',[status(thm)],['252','300'])).

thf('302',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
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
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['251','302'])).

thf('304',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['303','304','305'])).

thf('307',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['306'])).

thf('308',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['250','307'])).

thf('309',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['308','309','310'])).

thf('312',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['249','312'])).

thf('314',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['316'])).

thf('318',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['268','271'])).

thf('319',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r3_waybel_9 @ X33 @ ( sk_B @ X33 ) @ X34 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('320',plain,
    ( ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['320','321','322'])).

thf('324',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
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
    inference('sup-',[status(thm)],['317','324'])).

thf('326',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('328',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('329',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['326','329'])).

thf('331',plain,(
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

thf('332',plain,
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
    inference('sup-',[status(thm)],['330','331'])).

thf('333',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,
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
    inference(demod,[status(thm)],['332','333','334'])).

thf('336',plain,
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
    inference(simplify,[status(thm)],['335'])).

thf('337',plain,
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
    inference('sup-',[status(thm)],['248','336'])).

thf('338',plain,
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
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,
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
    inference('sup-',[status(thm)],['224','338'])).

thf('340',plain,
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
    inference(simplify,[status(thm)],['339'])).

thf('341',plain,
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
    inference('sup-',[status(thm)],['206','340'])).

thf('342',plain,
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
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,
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
    inference('sup-',[status(thm)],['182','342'])).

thf('344',plain,
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
    inference(simplify,[status(thm)],['343'])).

thf('345',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('346',plain,
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

thf('347',plain,(
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

thf('348',plain,
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
    inference('sup-',[status(thm)],['346','347'])).

thf('349',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('350',plain,
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
    inference(demod,[status(thm)],['348','349'])).

thf('351',plain,
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
    inference(simplify,[status(thm)],['350'])).

thf('352',plain,
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
    inference('sup-',[status(thm)],['345','351'])).

thf('353',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
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
    inference(demod,[status(thm)],['352','353','354'])).

thf('356',plain,
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
    inference(simplify,[status(thm)],['355'])).

thf('357',plain,
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
    inference('sup-',[status(thm)],['344','356'])).

thf('358',plain,
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
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
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
    inference('sup-',[status(thm)],['141','358'])).

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
    inference(demod,[status(thm)],['359','360','361'])).

thf('363',plain,
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
    inference(simplify,[status(thm)],['362'])).

thf('364',plain,
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
    inference('sup-',[status(thm)],['140','363'])).

thf('365',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,
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
    inference(demod,[status(thm)],['364','365','366'])).

thf('368',plain,
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
    inference(simplify,[status(thm)],['367'])).

thf('369',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
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
    inference(clc,[status(thm)],['368','369'])).

thf('371',plain,(
    ! [X33: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('372',plain,
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
    inference('sup-',[status(thm)],['370','371'])).

thf('373',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('374',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,
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
    inference(demod,[status(thm)],['372','373','374'])).

thf('376',plain,
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
    inference(simplify,[status(thm)],['375'])).

thf('377',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('378',plain,
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
    inference(clc,[status(thm)],['376','377'])).

thf('379',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('380',plain,
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
    inference('sup-',[status(thm)],['378','379'])).

thf('381',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','138','139','380'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sVbZp7for3
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 4.25/4.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.25/4.51  % Solved by: fo/fo7.sh
% 4.25/4.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.25/4.51  % done 5514 iterations in 4.049s
% 4.25/4.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.25/4.51  % SZS output start Refutation
% 4.25/4.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.25/4.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.25/4.51  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 4.25/4.51  thf(k6_yellow_6_type, type, k6_yellow_6: $i > $i).
% 4.25/4.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.25/4.51  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 4.25/4.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 4.25/4.51  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 4.25/4.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.25/4.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.25/4.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.25/4.51  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 4.25/4.51  thf(sk_B_type, type, sk_B: $i > $i).
% 4.25/4.51  thf(sk_A_type, type, sk_A: $i).
% 4.25/4.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.25/4.51  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 4.25/4.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.25/4.51  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 4.25/4.51  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 4.25/4.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 4.25/4.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.25/4.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.25/4.51  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 4.25/4.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.25/4.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.25/4.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.25/4.51  thf(t37_yellow19, conjecture,
% 4.25/4.51    (![A:$i]:
% 4.25/4.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.25/4.51       ( ( v1_compts_1 @ A ) <=>
% 4.25/4.51         ( ![B:$i]:
% 4.25/4.51           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.51               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.51             ( ?[C:$i]:
% 4.25/4.51               ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ))).
% 4.25/4.51  thf(zf_stmt_0, negated_conjecture,
% 4.25/4.51    (~( ![A:$i]:
% 4.25/4.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.25/4.51            ( l1_pre_topc @ A ) ) =>
% 4.25/4.51          ( ( v1_compts_1 @ A ) <=>
% 4.25/4.51            ( ![B:$i]:
% 4.25/4.51              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.51                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.51                ( ?[C:$i]:
% 4.25/4.51                  ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ) )),
% 4.25/4.51    inference('cnf.neg', [status(esa)], [t37_yellow19])).
% 4.25/4.51  thf('0', plain,
% 4.25/4.51      (![X37 : $i]:
% 4.25/4.51         ((v2_struct_0 @ X37)
% 4.25/4.51          | ~ (v4_orders_2 @ X37)
% 4.25/4.51          | ~ (v7_waybel_0 @ X37)
% 4.25/4.51          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.25/4.51          | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37)
% 4.25/4.51          | (v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('1', plain,
% 4.25/4.51      ((![X37 : $i]:
% 4.25/4.51          ((v2_struct_0 @ X37)
% 4.25/4.51           | ~ (v4_orders_2 @ X37)
% 4.25/4.51           | ~ (v7_waybel_0 @ X37)
% 4.25/4.51           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.25/4.51           | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))) | 
% 4.25/4.51       ((v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('split', [status(esa)], ['0'])).
% 4.25/4.51  thf('2', plain,
% 4.25/4.51      (![X36 : $i]:
% 4.25/4.51         (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 4.25/4.51          | ~ (v3_yellow_6 @ X36 @ sk_A)
% 4.25/4.51          | ~ (v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('3', plain,
% 4.25/4.51      ((![X36 : $i]:
% 4.25/4.51          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 4.25/4.51       ~ ((v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('split', [status(esa)], ['2'])).
% 4.25/4.51  thf('4', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('5', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('split', [status(esa)], ['4'])).
% 4.25/4.51  thf('6', plain, (((v7_waybel_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('7', plain, (((v7_waybel_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('split', [status(esa)], ['6'])).
% 4.25/4.51  thf('8', plain, (((v4_orders_2 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('9', plain, (((v4_orders_2 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('split', [status(esa)], ['8'])).
% 4.25/4.51  thf('10', plain, ((~ (v2_struct_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('11', plain, (~ ((v2_struct_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('split', [status(esa)], ['10'])).
% 4.25/4.51  thf('12', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['8'])).
% 4.25/4.51  thf('13', plain,
% 4.25/4.51      (![X37 : $i]:
% 4.25/4.51         ((v2_struct_0 @ X37)
% 4.25/4.51          | ~ (v4_orders_2 @ X37)
% 4.25/4.51          | ~ (v7_waybel_0 @ X37)
% 4.25/4.51          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.25/4.51          | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A)
% 4.25/4.51          | (v1_compts_1 @ sk_A))),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('14', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['13'])).
% 4.25/4.51  thf('15', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['6'])).
% 4.25/4.51  thf('16', plain,
% 4.25/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['4'])).
% 4.25/4.51  thf(l37_yellow19, axiom,
% 4.25/4.51    (![A:$i]:
% 4.25/4.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.25/4.51       ( ( v1_compts_1 @ A ) =>
% 4.25/4.51         ( ![B:$i]:
% 4.25/4.51           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.51               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.51             ( ?[C:$i]:
% 4.25/4.51               ( ( r3_waybel_9 @ A @ B @ C ) & 
% 4.25/4.51                 ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 4.25/4.51  thf('17', plain,
% 4.25/4.51      (![X31 : $i, X32 : $i]:
% 4.25/4.51         (~ (v1_compts_1 @ X31)
% 4.25/4.51          | (v2_struct_0 @ X32)
% 4.25/4.51          | ~ (v4_orders_2 @ X32)
% 4.25/4.51          | ~ (v7_waybel_0 @ X32)
% 4.25/4.51          | ~ (l1_waybel_0 @ X32 @ X31)
% 4.25/4.51          | (r3_waybel_9 @ X31 @ X32 @ (sk_C @ X32 @ X31))
% 4.25/4.51          | ~ (l1_pre_topc @ X31)
% 4.25/4.51          | ~ (v2_pre_topc @ X31)
% 4.25/4.51          | (v2_struct_0 @ X31))),
% 4.25/4.51      inference('cnf', [status(esa)], [l37_yellow19])).
% 4.25/4.51  thf('18', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.25/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.25/4.51         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['16', '17'])).
% 4.25/4.51  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('21', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('demod', [status(thm)], ['18', '19', '20'])).
% 4.25/4.51  thf('22', plain,
% 4.25/4.51      (((~ (v1_compts_1 @ sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_A)))
% 4.25/4.51         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['15', '21'])).
% 4.25/4.51  thf('23', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['14', '22'])).
% 4.25/4.51  thf('24', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['12', '23'])).
% 4.25/4.51  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('26', plain,
% 4.25/4.51      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['24', '25'])).
% 4.25/4.51  thf('27', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['8'])).
% 4.25/4.51  thf('28', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['13'])).
% 4.25/4.51  thf('29', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['6'])).
% 4.25/4.51  thf('30', plain,
% 4.25/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['4'])).
% 4.25/4.51  thf('31', plain,
% 4.25/4.51      (![X31 : $i, X32 : $i]:
% 4.25/4.51         (~ (v1_compts_1 @ X31)
% 4.25/4.51          | (v2_struct_0 @ X32)
% 4.25/4.51          | ~ (v4_orders_2 @ X32)
% 4.25/4.51          | ~ (v7_waybel_0 @ X32)
% 4.25/4.51          | ~ (l1_waybel_0 @ X32 @ X31)
% 4.25/4.51          | (m1_subset_1 @ (sk_C @ X32 @ X31) @ (u1_struct_0 @ X31))
% 4.25/4.51          | ~ (l1_pre_topc @ X31)
% 4.25/4.51          | ~ (v2_pre_topc @ X31)
% 4.25/4.51          | (v2_struct_0 @ X31))),
% 4.25/4.51      inference('cnf', [status(esa)], [l37_yellow19])).
% 4.25/4.51  thf('32', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.25/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.25/4.51         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['30', '31'])).
% 4.25/4.51  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('35', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 4.25/4.51  thf('36', plain,
% 4.25/4.51      (((~ (v1_compts_1 @ sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_A)))
% 4.25/4.51         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['29', '35'])).
% 4.25/4.51  thf('37', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['28', '36'])).
% 4.25/4.51  thf('38', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['27', '37'])).
% 4.25/4.51  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('40', plain,
% 4.25/4.51      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['38', '39'])).
% 4.25/4.51  thf(t32_waybel_9, axiom,
% 4.25/4.51    (![A:$i]:
% 4.25/4.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.25/4.51       ( ![B:$i]:
% 4.25/4.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.51             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.51           ( ![C:$i]:
% 4.25/4.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.25/4.51               ( ~( ( r3_waybel_9 @ A @ B @ C ) & 
% 4.25/4.51                    ( ![D:$i]:
% 4.25/4.51                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 4.25/4.51                        ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.25/4.51  thf('41', plain,
% 4.25/4.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.25/4.51         ((v2_struct_0 @ X28)
% 4.25/4.51          | ~ (v4_orders_2 @ X28)
% 4.25/4.51          | ~ (v7_waybel_0 @ X28)
% 4.25/4.51          | ~ (l1_waybel_0 @ X28 @ X29)
% 4.25/4.51          | (m2_yellow_6 @ (sk_D_1 @ X30 @ X28 @ X29) @ X29 @ X28)
% 4.25/4.51          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 4.25/4.51          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 4.25/4.51          | ~ (l1_pre_topc @ X29)
% 4.25/4.51          | ~ (v2_pre_topc @ X29)
% 4.25/4.51          | (v2_struct_0 @ X29))),
% 4.25/4.51      inference('cnf', [status(esa)], [t32_waybel_9])).
% 4.25/4.51  thf('42', plain,
% 4.25/4.51      ((![X0 : $i]:
% 4.25/4.51          ((v2_struct_0 @ sk_B_1)
% 4.25/4.51           | (v2_struct_0 @ sk_A)
% 4.25/4.51           | ~ (v2_pre_topc @ sk_A)
% 4.25/4.51           | ~ (l1_pre_topc @ sk_A)
% 4.25/4.51           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 4.25/4.51              sk_A @ X0)
% 4.25/4.51           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.25/4.51           | ~ (v7_waybel_0 @ X0)
% 4.25/4.51           | ~ (v4_orders_2 @ X0)
% 4.25/4.51           | (v2_struct_0 @ X0)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['40', '41'])).
% 4.25/4.51  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('45', plain,
% 4.25/4.51      ((![X0 : $i]:
% 4.25/4.51          ((v2_struct_0 @ sk_B_1)
% 4.25/4.51           | (v2_struct_0 @ sk_A)
% 4.25/4.51           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 4.25/4.51           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 4.25/4.51              sk_A @ X0)
% 4.25/4.51           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.25/4.51           | ~ (v7_waybel_0 @ X0)
% 4.25/4.51           | ~ (v4_orders_2 @ X0)
% 4.25/4.51           | (v2_struct_0 @ X0)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 4.25/4.51  thf('46', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 4.25/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['26', '45'])).
% 4.25/4.51  thf('47', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['8'])).
% 4.25/4.51  thf('48', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['6'])).
% 4.25/4.51  thf('49', plain,
% 4.25/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['4'])).
% 4.25/4.51  thf('50', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 4.25/4.51  thf('51', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('simplify', [status(thm)], ['50'])).
% 4.25/4.51  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('53', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['51', '52'])).
% 4.25/4.51  thf(dt_m2_yellow_6, axiom,
% 4.25/4.51    (![A:$i,B:$i]:
% 4.25/4.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 4.25/4.51         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.51         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.51       ( ![C:$i]:
% 4.25/4.51         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 4.25/4.51           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 4.25/4.51             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 4.25/4.51  thf('54', plain,
% 4.25/4.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.25/4.51         (~ (l1_struct_0 @ X16)
% 4.25/4.51          | (v2_struct_0 @ X16)
% 4.25/4.51          | (v2_struct_0 @ X17)
% 4.25/4.51          | ~ (v4_orders_2 @ X17)
% 4.25/4.51          | ~ (v7_waybel_0 @ X17)
% 4.25/4.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.25/4.51          | (v4_orders_2 @ X18)
% 4.25/4.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.25/4.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.25/4.51  thf('55', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | ~ (l1_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['53', '54'])).
% 4.25/4.51  thf('56', plain,
% 4.25/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['4'])).
% 4.25/4.51  thf('57', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['6'])).
% 4.25/4.51  thf('58', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['8'])).
% 4.25/4.51  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf(dt_l1_pre_topc, axiom,
% 4.25/4.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 4.25/4.51  thf('60', plain,
% 4.25/4.51      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 4.25/4.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 4.25/4.51  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 4.25/4.51      inference('sup-', [status(thm)], ['59', '60'])).
% 4.25/4.51  thf('62', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('demod', [status(thm)], ['55', '56', '57', '58', '61'])).
% 4.25/4.51  thf('63', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('simplify', [status(thm)], ['62'])).
% 4.25/4.51  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('65', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['63', '64'])).
% 4.25/4.51  thf('66', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['51', '52'])).
% 4.25/4.51  thf('67', plain,
% 4.25/4.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.25/4.51         (~ (l1_struct_0 @ X16)
% 4.25/4.51          | (v2_struct_0 @ X16)
% 4.25/4.51          | (v2_struct_0 @ X17)
% 4.25/4.51          | ~ (v4_orders_2 @ X17)
% 4.25/4.51          | ~ (v7_waybel_0 @ X17)
% 4.25/4.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.25/4.51          | (v7_waybel_0 @ X18)
% 4.25/4.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.25/4.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.25/4.51  thf('68', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | ~ (l1_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['66', '67'])).
% 4.25/4.51  thf('69', plain,
% 4.25/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['4'])).
% 4.25/4.51  thf('70', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['6'])).
% 4.25/4.51  thf('71', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['8'])).
% 4.25/4.51  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 4.25/4.51      inference('sup-', [status(thm)], ['59', '60'])).
% 4.25/4.51  thf('73', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 4.25/4.51  thf('74', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('simplify', [status(thm)], ['73'])).
% 4.25/4.51  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('76', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['74', '75'])).
% 4.25/4.51  thf('77', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['51', '52'])).
% 4.25/4.51  thf('78', plain,
% 4.25/4.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.25/4.51         (~ (l1_struct_0 @ X16)
% 4.25/4.51          | (v2_struct_0 @ X16)
% 4.25/4.51          | (v2_struct_0 @ X17)
% 4.25/4.51          | ~ (v4_orders_2 @ X17)
% 4.25/4.51          | ~ (v7_waybel_0 @ X17)
% 4.25/4.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.25/4.51          | (l1_waybel_0 @ X18 @ X16)
% 4.25/4.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.25/4.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.25/4.51  thf('79', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)
% 4.25/4.51         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 4.25/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.25/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | ~ (l1_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['77', '78'])).
% 4.25/4.51  thf('80', plain,
% 4.25/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.25/4.51      inference('split', [status(esa)], ['4'])).
% 4.25/4.51  thf('81', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['6'])).
% 4.25/4.51  thf('82', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('split', [status(esa)], ['8'])).
% 4.25/4.51  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 4.25/4.51      inference('sup-', [status(thm)], ['59', '60'])).
% 4.25/4.51  thf('84', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 4.25/4.51  thf('85', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('simplify', [status(thm)], ['84'])).
% 4.25/4.51  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('87', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('clc', [status(thm)], ['85', '86'])).
% 4.25/4.51  thf(d19_yellow_6, axiom,
% 4.25/4.51    (![A:$i]:
% 4.25/4.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.25/4.51       ( ![B:$i]:
% 4.25/4.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.25/4.51             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.25/4.51           ( ( v3_yellow_6 @ B @ A ) <=>
% 4.25/4.51             ( ( k10_yellow_6 @ A @ B ) != ( k1_xboole_0 ) ) ) ) ) ))).
% 4.25/4.51  thf('88', plain,
% 4.25/4.51      (![X19 : $i, X20 : $i]:
% 4.25/4.51         ((v2_struct_0 @ X19)
% 4.25/4.51          | ~ (v4_orders_2 @ X19)
% 4.25/4.51          | ~ (v7_waybel_0 @ X19)
% 4.25/4.51          | ~ (l1_waybel_0 @ X19 @ X20)
% 4.25/4.51          | ((k10_yellow_6 @ X20 @ X19) = (k1_xboole_0))
% 4.25/4.51          | (v3_yellow_6 @ X19 @ X20)
% 4.25/4.51          | ~ (l1_pre_topc @ X20)
% 4.25/4.51          | ~ (v2_pre_topc @ X20)
% 4.25/4.51          | (v2_struct_0 @ X20))),
% 4.25/4.51      inference('cnf', [status(esa)], [d19_yellow_6])).
% 4.25/4.51  thf('89', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.25/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.25/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)
% 4.25/4.51         | ((k10_yellow_6 @ sk_A @ 
% 4.25/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 4.25/4.51         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['87', '88'])).
% 4.25/4.51  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 4.25/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.25/4.51  thf('92', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)
% 4.25/4.51         | ((k10_yellow_6 @ sk_A @ 
% 4.25/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 4.25/4.51         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('demod', [status(thm)], ['89', '90', '91'])).
% 4.25/4.51  thf('93', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.25/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | ((k10_yellow_6 @ sk_A @ 
% 4.25/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 4.25/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_A)
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.25/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.25/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.25/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.25/4.51      inference('sup-', [status(thm)], ['76', '92'])).
% 4.25/4.51  thf('94', plain,
% 4.25/4.51      ((((v2_struct_0 @ sk_A)
% 4.25/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.25/4.51            sk_A)
% 4.25/4.51         | ((k10_yellow_6 @ sk_A @ 
% 4.25/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 4.25/4.51         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.25/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.25/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('simplify', [status(thm)], ['93'])).
% 4.34/4.51  thf('95', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | ((k10_yellow_6 @ sk_A @ 
% 4.34/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 4.34/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['65', '94'])).
% 4.34/4.51  thf('96', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            sk_A)
% 4.34/4.51         | ((k10_yellow_6 @ sk_A @ 
% 4.34/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('simplify', [status(thm)], ['95'])).
% 4.34/4.51  thf('97', plain,
% 4.34/4.51      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['24', '25'])).
% 4.34/4.51  thf('98', plain,
% 4.34/4.51      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['38', '39'])).
% 4.34/4.51  thf('99', plain,
% 4.34/4.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.34/4.51         ((v2_struct_0 @ X28)
% 4.34/4.51          | ~ (v4_orders_2 @ X28)
% 4.34/4.51          | ~ (v7_waybel_0 @ X28)
% 4.34/4.51          | ~ (l1_waybel_0 @ X28 @ X29)
% 4.34/4.51          | (r2_hidden @ X30 @ 
% 4.34/4.51             (k10_yellow_6 @ X29 @ (sk_D_1 @ X30 @ X28 @ X29)))
% 4.34/4.51          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 4.34/4.51          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 4.34/4.51          | ~ (l1_pre_topc @ X29)
% 4.34/4.51          | ~ (v2_pre_topc @ X29)
% 4.34/4.51          | (v2_struct_0 @ X29))),
% 4.34/4.51      inference('cnf', [status(esa)], [t32_waybel_9])).
% 4.34/4.51  thf('100', plain,
% 4.34/4.51      ((![X0 : $i]:
% 4.34/4.51          ((v2_struct_0 @ sk_B_1)
% 4.34/4.51           | (v2_struct_0 @ sk_A)
% 4.34/4.51           | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51           | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 4.34/4.51           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 4.34/4.51              (k10_yellow_6 @ sk_A @ 
% 4.34/4.51               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 4.34/4.51           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.34/4.51           | ~ (v7_waybel_0 @ X0)
% 4.34/4.51           | ~ (v4_orders_2 @ X0)
% 4.34/4.51           | (v2_struct_0 @ X0)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['98', '99'])).
% 4.34/4.51  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('103', plain,
% 4.34/4.51      ((![X0 : $i]:
% 4.34/4.51          ((v2_struct_0 @ sk_B_1)
% 4.34/4.51           | (v2_struct_0 @ sk_A)
% 4.34/4.51           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 4.34/4.51           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 4.34/4.51              (k10_yellow_6 @ sk_A @ 
% 4.34/4.51               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 4.34/4.51           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.34/4.51           | ~ (v7_waybel_0 @ X0)
% 4.34/4.51           | ~ (v4_orders_2 @ X0)
% 4.34/4.51           | (v2_struct_0 @ X0)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('demod', [status(thm)], ['100', '101', '102'])).
% 4.34/4.51  thf('104', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)
% 4.34/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.34/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.34/4.51         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 4.34/4.51         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            (k10_yellow_6 @ sk_A @ 
% 4.34/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['97', '103'])).
% 4.34/4.51  thf('105', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('split', [status(esa)], ['8'])).
% 4.34/4.51  thf('106', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.34/4.51      inference('split', [status(esa)], ['6'])).
% 4.34/4.51  thf('107', plain,
% 4.34/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.34/4.51      inference('split', [status(esa)], ['4'])).
% 4.34/4.51  thf('108', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            (k10_yellow_6 @ sk_A @ 
% 4.34/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 4.34/4.51  thf('109', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            (k10_yellow_6 @ sk_A @ 
% 4.34/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('simplify', [status(thm)], ['108'])).
% 4.34/4.51  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('111', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            (k10_yellow_6 @ sk_A @ 
% 4.34/4.51             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['109', '110'])).
% 4.34/4.51  thf(t7_ordinal1, axiom,
% 4.34/4.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.34/4.51  thf('112', plain,
% 4.34/4.51      (![X11 : $i, X12 : $i]:
% 4.34/4.51         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 4.34/4.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.34/4.51  thf('113', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | ~ (r1_tarski @ 
% 4.34/4.51              (k10_yellow_6 @ sk_A @ 
% 4.34/4.51               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) @ 
% 4.34/4.51              (sk_C @ sk_B_1 @ sk_A))))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['111', '112'])).
% 4.34/4.51  thf('114', plain,
% 4.34/4.51      (((~ (r1_tarski @ k1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['96', '113'])).
% 4.34/4.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.34/4.51  thf('115', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.34/4.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.34/4.51  thf('116', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('demod', [status(thm)], ['114', '115'])).
% 4.34/4.51  thf('117', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('simplify', [status(thm)], ['116'])).
% 4.34/4.51  thf('118', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            sk_A @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['51', '52'])).
% 4.34/4.51  thf('119', plain,
% 4.34/4.51      ((![X36 : $i]:
% 4.34/4.51          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A)))
% 4.34/4.51         <= ((![X36 : $i]:
% 4.34/4.51                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 4.34/4.51                 | ~ (v3_yellow_6 @ X36 @ sk_A))))),
% 4.34/4.51      inference('split', [status(esa)], ['2'])).
% 4.34/4.51  thf('120', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | ~ (v3_yellow_6 @ 
% 4.34/4.51              (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ sk_A)))
% 4.34/4.51         <= ((![X36 : $i]:
% 4.34/4.51                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 4.34/4.51                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 4.34/4.51             ((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['118', '119'])).
% 4.34/4.51  thf('121', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= ((![X36 : $i]:
% 4.34/4.51                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 4.34/4.51                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 4.34/4.51             ((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['117', '120'])).
% 4.34/4.51  thf('122', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= ((![X36 : $i]:
% 4.34/4.51                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 4.34/4.51                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 4.34/4.51             ((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('simplify', [status(thm)], ['121'])).
% 4.34/4.51  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('124', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 4.34/4.51         <= ((![X36 : $i]:
% 4.34/4.51                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 4.34/4.51                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 4.34/4.51             ((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['122', '123'])).
% 4.34/4.51  thf('125', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 4.34/4.51            sk_A @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['51', '52'])).
% 4.34/4.51  thf('126', plain,
% 4.34/4.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.34/4.51         (~ (l1_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X17)
% 4.34/4.51          | ~ (v4_orders_2 @ X17)
% 4.34/4.51          | ~ (v7_waybel_0 @ X17)
% 4.34/4.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.34/4.51          | ~ (v2_struct_0 @ X18)
% 4.34/4.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.34/4.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.34/4.51  thf('127', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ sk_B_1)
% 4.34/4.51         | ~ (v4_orders_2 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (l1_struct_0 @ sk_A)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('sup-', [status(thm)], ['125', '126'])).
% 4.34/4.51  thf('128', plain,
% 4.34/4.51      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 4.34/4.51      inference('split', [status(esa)], ['4'])).
% 4.34/4.51  thf('129', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 4.34/4.51      inference('split', [status(esa)], ['6'])).
% 4.34/4.51  thf('130', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('split', [status(esa)], ['8'])).
% 4.34/4.51  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 4.34/4.51      inference('sup-', [status(thm)], ['59', '60'])).
% 4.34/4.51  thf('132', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 4.34/4.51  thf('133', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_B_1)))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('simplify', [status(thm)], ['132'])).
% 4.34/4.51  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('135', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_B_1)
% 4.34/4.51         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 4.34/4.51         <= (((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['133', '134'])).
% 4.34/4.51  thf('136', plain,
% 4.34/4.51      (((v2_struct_0 @ sk_B_1))
% 4.34/4.51         <= ((![X36 : $i]:
% 4.34/4.51                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 4.34/4.51                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 4.34/4.51             ((v1_compts_1 @ sk_A)) & 
% 4.34/4.51             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 4.34/4.51             ((v7_waybel_0 @ sk_B_1)) & 
% 4.34/4.51             ((v4_orders_2 @ sk_B_1)))),
% 4.34/4.51      inference('clc', [status(thm)], ['124', '135'])).
% 4.34/4.51  thf('137', plain,
% 4.34/4.51      ((~ (v2_struct_0 @ sk_B_1)) <= (~ ((v2_struct_0 @ sk_B_1)))),
% 4.34/4.51      inference('split', [status(esa)], ['10'])).
% 4.34/4.51  thf('138', plain,
% 4.34/4.51      (~ ((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A)) | 
% 4.34/4.51       ~
% 4.34/4.51       (![X36 : $i]:
% 4.34/4.51          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 4.34/4.51       ~ ((v7_waybel_0 @ sk_B_1)) | ~ ((v4_orders_2 @ sk_B_1)) | 
% 4.34/4.51       ((v2_struct_0 @ sk_B_1))),
% 4.34/4.51      inference('sup-', [status(thm)], ['136', '137'])).
% 4.34/4.51  thf('139', plain,
% 4.34/4.51      ((![X37 : $i]:
% 4.34/4.51          ((v2_struct_0 @ X37)
% 4.34/4.51           | ~ (v4_orders_2 @ X37)
% 4.34/4.51           | ~ (v7_waybel_0 @ X37)
% 4.34/4.51           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51           | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) | 
% 4.34/4.51       ((v1_compts_1 @ sk_A))),
% 4.34/4.51      inference('split', [status(esa)], ['13'])).
% 4.34/4.51  thf(t36_yellow19, axiom,
% 4.34/4.51    (![A:$i]:
% 4.34/4.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.34/4.51       ( ( v1_compts_1 @ A ) <=>
% 4.34/4.51         ( ![B:$i]:
% 4.34/4.51           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.34/4.51               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.34/4.51             ( ~( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) ) & 
% 4.34/4.51                  ( ![C:$i]:
% 4.34/4.51                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.34/4.51                      ( ~( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ) ) ) ))).
% 4.34/4.51  thf('140', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v7_waybel_0 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('141', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v4_orders_2 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('142', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v7_waybel_0 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('143', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v4_orders_2 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('144', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('145', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v4_orders_2 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('146', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v7_waybel_0 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('147', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('148', plain,
% 4.34/4.51      ((![X37 : $i]:
% 4.34/4.51          ((v2_struct_0 @ X37)
% 4.34/4.51           | ~ (v4_orders_2 @ X37)
% 4.34/4.51           | ~ (v7_waybel_0 @ X37)
% 4.34/4.51           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51           | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('split', [status(esa)], ['0'])).
% 4.34/4.51  thf('149', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['147', '148'])).
% 4.34/4.51  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('152', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['149', '150', '151'])).
% 4.34/4.51  thf('153', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['146', '152'])).
% 4.34/4.51  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('156', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['153', '154', '155'])).
% 4.34/4.51  thf('157', plain,
% 4.34/4.51      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['156'])).
% 4.34/4.51  thf('158', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['145', '157'])).
% 4.34/4.51  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('161', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['158', '159', '160'])).
% 4.34/4.51  thf('162', plain,
% 4.34/4.51      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['161'])).
% 4.34/4.51  thf('163', plain,
% 4.34/4.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.34/4.51         (~ (l1_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X17)
% 4.34/4.51          | ~ (v4_orders_2 @ X17)
% 4.34/4.51          | ~ (v7_waybel_0 @ X17)
% 4.34/4.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.34/4.51          | (v7_waybel_0 @ X18)
% 4.34/4.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.34/4.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.34/4.51  thf('164', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (l1_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['162', '163'])).
% 4.34/4.51  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 4.34/4.51      inference('sup-', [status(thm)], ['59', '60'])).
% 4.34/4.51  thf('166', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['164', '165'])).
% 4.34/4.51  thf('167', plain,
% 4.34/4.51      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['166'])).
% 4.34/4.51  thf('168', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['144', '167'])).
% 4.34/4.51  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('171', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['168', '169', '170'])).
% 4.34/4.51  thf('172', plain,
% 4.34/4.51      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['171'])).
% 4.34/4.51  thf('173', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['143', '172'])).
% 4.34/4.51  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('176', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['173', '174', '175'])).
% 4.34/4.51  thf('177', plain,
% 4.34/4.51      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['176'])).
% 4.34/4.51  thf('178', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['142', '177'])).
% 4.34/4.51  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('181', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['178', '179', '180'])).
% 4.34/4.51  thf('182', plain,
% 4.34/4.51      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['181'])).
% 4.34/4.51  thf('183', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v4_orders_2 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('184', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v7_waybel_0 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('185', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('186', plain,
% 4.34/4.51      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['161'])).
% 4.34/4.51  thf('187', plain,
% 4.34/4.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.34/4.51         (~ (l1_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X17)
% 4.34/4.51          | ~ (v4_orders_2 @ X17)
% 4.34/4.51          | ~ (v7_waybel_0 @ X17)
% 4.34/4.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.34/4.51          | (v4_orders_2 @ X18)
% 4.34/4.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.34/4.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.34/4.51  thf('188', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (l1_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['186', '187'])).
% 4.34/4.51  thf('189', plain, ((l1_struct_0 @ sk_A)),
% 4.34/4.51      inference('sup-', [status(thm)], ['59', '60'])).
% 4.34/4.51  thf('190', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['188', '189'])).
% 4.34/4.51  thf('191', plain,
% 4.34/4.51      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['190'])).
% 4.34/4.51  thf('192', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['185', '191'])).
% 4.34/4.51  thf('193', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('195', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['192', '193', '194'])).
% 4.34/4.51  thf('196', plain,
% 4.34/4.51      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['195'])).
% 4.34/4.51  thf('197', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['184', '196'])).
% 4.34/4.51  thf('198', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('200', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['197', '198', '199'])).
% 4.34/4.51  thf('201', plain,
% 4.34/4.51      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['200'])).
% 4.34/4.51  thf('202', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['183', '201'])).
% 4.34/4.51  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('205', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['202', '203', '204'])).
% 4.34/4.51  thf('206', plain,
% 4.34/4.51      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['205'])).
% 4.34/4.51  thf('207', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v4_orders_2 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('208', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v7_waybel_0 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('209', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('210', plain,
% 4.34/4.51      ((![X37 : $i]:
% 4.34/4.51          ((v2_struct_0 @ X37)
% 4.34/4.51           | ~ (v4_orders_2 @ X37)
% 4.34/4.51           | ~ (v7_waybel_0 @ X37)
% 4.34/4.51           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51           | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('split', [status(esa)], ['13'])).
% 4.34/4.51  thf('211', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['209', '210'])).
% 4.34/4.51  thf('212', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('214', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('demod', [status(thm)], ['211', '212', '213'])).
% 4.34/4.51  thf('215', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['208', '214'])).
% 4.34/4.51  thf('216', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('218', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('demod', [status(thm)], ['215', '216', '217'])).
% 4.34/4.51  thf('219', plain,
% 4.34/4.51      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['218'])).
% 4.34/4.51  thf('220', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['207', '219'])).
% 4.34/4.51  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('223', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('demod', [status(thm)], ['220', '221', '222'])).
% 4.34/4.51  thf('224', plain,
% 4.34/4.51      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['223'])).
% 4.34/4.51  thf('225', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v7_waybel_0 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('226', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((v4_orders_2 @ (sk_B @ X33))
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('227', plain,
% 4.34/4.51      (![X33 : $i]:
% 4.34/4.51         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 4.34/4.51          | (v1_compts_1 @ X33)
% 4.34/4.51          | ~ (l1_pre_topc @ X33)
% 4.34/4.51          | ~ (v2_pre_topc @ X33)
% 4.34/4.51          | (v2_struct_0 @ X33))),
% 4.34/4.51      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.51  thf('228', plain,
% 4.34/4.51      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['161'])).
% 4.34/4.51  thf('229', plain,
% 4.34/4.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.34/4.51         (~ (l1_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X16)
% 4.34/4.51          | (v2_struct_0 @ X17)
% 4.34/4.51          | ~ (v4_orders_2 @ X17)
% 4.34/4.51          | ~ (v7_waybel_0 @ X17)
% 4.34/4.51          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.34/4.51          | (l1_waybel_0 @ X18 @ X16)
% 4.34/4.51          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.34/4.51      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.34/4.51  thf('230', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (l1_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['228', '229'])).
% 4.34/4.51  thf('231', plain, ((l1_struct_0 @ sk_A)),
% 4.34/4.51      inference('sup-', [status(thm)], ['59', '60'])).
% 4.34/4.51  thf('232', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['230', '231'])).
% 4.34/4.51  thf('233', plain,
% 4.34/4.51      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['232'])).
% 4.34/4.51  thf('234', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['227', '233'])).
% 4.34/4.51  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('237', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('demod', [status(thm)], ['234', '235', '236'])).
% 4.34/4.51  thf('238', plain,
% 4.34/4.51      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('simplify', [status(thm)], ['237'])).
% 4.34/4.51  thf('239', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.51         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.51                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.51                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.51      inference('sup-', [status(thm)], ['226', '238'])).
% 4.34/4.51  thf('240', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.51  thf('242', plain,
% 4.34/4.51      ((((v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ sk_A)
% 4.34/4.51         | (v1_compts_1 @ sk_A)
% 4.34/4.51         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.51         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.51         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.51         <= ((![X37 : $i]:
% 4.34/4.51                ((v2_struct_0 @ X37)
% 4.34/4.51                 | ~ (v4_orders_2 @ X37)
% 4.34/4.51                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['239', '240', '241'])).
% 4.34/4.52  thf('243', plain,
% 4.34/4.52      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['242'])).
% 4.34/4.52  thf('244', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['225', '243'])).
% 4.34/4.52  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('247', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['244', '245', '246'])).
% 4.34/4.52  thf('248', plain,
% 4.34/4.52      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['247'])).
% 4.34/4.52  thf('249', plain,
% 4.34/4.52      (![X33 : $i]:
% 4.34/4.52         ((v7_waybel_0 @ (sk_B @ X33))
% 4.34/4.52          | (v1_compts_1 @ X33)
% 4.34/4.52          | ~ (l1_pre_topc @ X33)
% 4.34/4.52          | ~ (v2_pre_topc @ X33)
% 4.34/4.52          | (v2_struct_0 @ X33))),
% 4.34/4.52      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.52  thf('250', plain,
% 4.34/4.52      (![X33 : $i]:
% 4.34/4.52         ((v4_orders_2 @ (sk_B @ X33))
% 4.34/4.52          | (v1_compts_1 @ X33)
% 4.34/4.52          | ~ (l1_pre_topc @ X33)
% 4.34/4.52          | ~ (v2_pre_topc @ X33)
% 4.34/4.52          | (v2_struct_0 @ X33))),
% 4.34/4.52      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.52  thf('251', plain,
% 4.34/4.52      (![X33 : $i]:
% 4.34/4.52         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 4.34/4.52          | (v1_compts_1 @ X33)
% 4.34/4.52          | ~ (l1_pre_topc @ X33)
% 4.34/4.52          | ~ (v2_pre_topc @ X33)
% 4.34/4.52          | (v2_struct_0 @ X33))),
% 4.34/4.52      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.52  thf('252', plain,
% 4.34/4.52      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['161'])).
% 4.34/4.52  thf('253', plain,
% 4.34/4.52      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['181'])).
% 4.34/4.52  thf('254', plain,
% 4.34/4.52      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['205'])).
% 4.34/4.52  thf('255', plain,
% 4.34/4.52      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['247'])).
% 4.34/4.52  thf('256', plain,
% 4.34/4.52      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['181'])).
% 4.34/4.52  thf('257', plain,
% 4.34/4.52      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['205'])).
% 4.34/4.52  thf('258', plain,
% 4.34/4.52      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['247'])).
% 4.34/4.52  thf(dt_k10_yellow_6, axiom,
% 4.34/4.52    (![A:$i,B:$i]:
% 4.34/4.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.34/4.52         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 4.34/4.52         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.34/4.52       ( m1_subset_1 @
% 4.34/4.52         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.34/4.52  thf('259', plain,
% 4.34/4.52      (![X14 : $i, X15 : $i]:
% 4.34/4.52         (~ (l1_pre_topc @ X14)
% 4.34/4.52          | ~ (v2_pre_topc @ X14)
% 4.34/4.52          | (v2_struct_0 @ X14)
% 4.34/4.52          | (v2_struct_0 @ X15)
% 4.34/4.52          | ~ (v4_orders_2 @ X15)
% 4.34/4.52          | ~ (v7_waybel_0 @ X15)
% 4.34/4.52          | ~ (l1_waybel_0 @ X15 @ X14)
% 4.34/4.52          | (m1_subset_1 @ (k10_yellow_6 @ X14 @ X15) @ 
% 4.34/4.52             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 4.34/4.52      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 4.34/4.52  thf('260', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['258', '259'])).
% 4.34/4.52  thf('261', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('262', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('263', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['260', '261', '262'])).
% 4.34/4.52  thf('264', plain,
% 4.34/4.52      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['263'])).
% 4.34/4.52  thf('265', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['257', '264'])).
% 4.34/4.52  thf('266', plain,
% 4.34/4.52      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['265'])).
% 4.34/4.52  thf('267', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['256', '266'])).
% 4.34/4.52  thf('268', plain,
% 4.34/4.52      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['267'])).
% 4.34/4.52  thf(t4_subset_1, axiom,
% 4.34/4.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.34/4.52  thf('269', plain,
% 4.34/4.52      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 4.34/4.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.34/4.52  thf(t7_subset_1, axiom,
% 4.34/4.52    (![A:$i,B:$i]:
% 4.34/4.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.34/4.52       ( ![C:$i]:
% 4.34/4.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.34/4.52           ( ( ![D:$i]:
% 4.34/4.52               ( ( m1_subset_1 @ D @ A ) =>
% 4.34/4.52                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 4.34/4.52             ( r1_tarski @ B @ C ) ) ) ) ))).
% 4.34/4.52  thf('270', plain,
% 4.34/4.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.34/4.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 4.34/4.52          | (r1_tarski @ X7 @ X5)
% 4.34/4.52          | (m1_subset_1 @ (sk_D @ X5 @ X7 @ X6) @ X6)
% 4.34/4.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 4.34/4.52      inference('cnf', [status(esa)], [t7_subset_1])).
% 4.34/4.52  thf('271', plain,
% 4.34/4.52      (![X0 : $i, X1 : $i]:
% 4.34/4.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 4.34/4.52          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 4.34/4.52          | (r1_tarski @ X1 @ k1_xboole_0))),
% 4.34/4.52      inference('sup-', [status(thm)], ['269', '270'])).
% 4.34/4.52  thf('272', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (m1_subset_1 @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)) @ 
% 4.34/4.52            (u1_struct_0 @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['268', '271'])).
% 4.34/4.52  thf('273', plain,
% 4.34/4.52      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['267'])).
% 4.34/4.52  thf('274', plain,
% 4.34/4.52      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 4.34/4.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.34/4.52  thf('275', plain,
% 4.34/4.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.34/4.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 4.34/4.52          | (r1_tarski @ X7 @ X5)
% 4.34/4.52          | (r2_hidden @ (sk_D @ X5 @ X7 @ X6) @ X7)
% 4.34/4.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 4.34/4.52      inference('cnf', [status(esa)], [t7_subset_1])).
% 4.34/4.52  thf('276', plain,
% 4.34/4.52      (![X0 : $i, X1 : $i]:
% 4.34/4.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 4.34/4.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 4.34/4.52          | (r1_tarski @ X1 @ k1_xboole_0))),
% 4.34/4.52      inference('sup-', [status(thm)], ['274', '275'])).
% 4.34/4.52  thf('277', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (r2_hidden @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)) @ 
% 4.34/4.52            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['273', '276'])).
% 4.34/4.52  thf(t29_waybel_9, axiom,
% 4.34/4.52    (![A:$i]:
% 4.34/4.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.34/4.52       ( ![B:$i]:
% 4.34/4.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.34/4.52             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.34/4.52           ( ![C:$i]:
% 4.34/4.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.34/4.52               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) =>
% 4.34/4.52                 ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 4.34/4.52  thf('278', plain,
% 4.34/4.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.34/4.52         ((v2_struct_0 @ X21)
% 4.34/4.52          | ~ (v4_orders_2 @ X21)
% 4.34/4.52          | ~ (v7_waybel_0 @ X21)
% 4.34/4.52          | ~ (l1_waybel_0 @ X21 @ X22)
% 4.34/4.52          | ~ (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 4.34/4.52          | (r3_waybel_9 @ X22 @ X21 @ X23)
% 4.34/4.52          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 4.34/4.52          | ~ (l1_pre_topc @ X22)
% 4.34/4.52          | ~ (v2_pre_topc @ X22)
% 4.34/4.52          | (v2_struct_0 @ X22))),
% 4.34/4.52      inference('cnf', [status(esa)], [t29_waybel_9])).
% 4.34/4.52  thf('279', plain,
% 4.34/4.52      ((((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52          k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | ~ (m1_subset_1 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)) @ 
% 4.34/4.52              (u1_struct_0 @ sk_A))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['277', '278'])).
% 4.34/4.52  thf('280', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('281', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('282', plain,
% 4.34/4.52      ((((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52          k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (m1_subset_1 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)) @ 
% 4.34/4.52              (u1_struct_0 @ sk_A))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['279', '280', '281'])).
% 4.34/4.52  thf('283', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (m1_subset_1 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)) @ 
% 4.34/4.52              (u1_struct_0 @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['282'])).
% 4.34/4.52  thf('284', plain,
% 4.34/4.52      ((((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52          k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['272', '283'])).
% 4.34/4.52  thf('285', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['284'])).
% 4.34/4.52  thf('286', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['255', '285'])).
% 4.34/4.52  thf('287', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['286'])).
% 4.34/4.52  thf('288', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['254', '287'])).
% 4.34/4.52  thf('289', plain,
% 4.34/4.52      (((~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['288'])).
% 4.34/4.52  thf('290', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['253', '289'])).
% 4.34/4.52  thf('291', plain,
% 4.34/4.52      ((((r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 4.34/4.52          (sk_D @ k1_xboole_0 @ 
% 4.34/4.52           (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52           (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['290'])).
% 4.34/4.52  thf('292', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (m1_subset_1 @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)) @ 
% 4.34/4.52            (u1_struct_0 @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['268', '271'])).
% 4.34/4.52  thf(t31_waybel_9, axiom,
% 4.34/4.52    (![A:$i]:
% 4.34/4.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.34/4.52       ( ![B:$i]:
% 4.34/4.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 4.34/4.52             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 4.34/4.52           ( ![C:$i]:
% 4.34/4.52             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 4.34/4.52               ( ![D:$i]:
% 4.34/4.52                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.34/4.52                   ( ( r3_waybel_9 @ A @ C @ D ) => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 4.34/4.52  thf('293', plain,
% 4.34/4.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 4.34/4.52         ((v2_struct_0 @ X24)
% 4.34/4.52          | ~ (v4_orders_2 @ X24)
% 4.34/4.52          | ~ (v7_waybel_0 @ X24)
% 4.34/4.52          | ~ (l1_waybel_0 @ X24 @ X25)
% 4.34/4.52          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 4.34/4.52          | (r3_waybel_9 @ X25 @ X24 @ X26)
% 4.34/4.52          | ~ (r3_waybel_9 @ X25 @ X27 @ X26)
% 4.34/4.52          | ~ (m2_yellow_6 @ X27 @ X25 @ X24)
% 4.34/4.52          | ~ (l1_pre_topc @ X25)
% 4.34/4.52          | ~ (v2_pre_topc @ X25)
% 4.34/4.52          | (v2_struct_0 @ X25))),
% 4.34/4.52      inference('cnf', [status(esa)], [t31_waybel_9])).
% 4.34/4.52  thf('294', plain,
% 4.34/4.52      ((![X0 : $i, X1 : $i]:
% 4.34/4.52          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52           | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52           | (v1_compts_1 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ sk_A)
% 4.34/4.52           | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52           | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 4.34/4.52           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 4.34/4.52                (sk_D @ k1_xboole_0 @ 
% 4.34/4.52                 (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52                 (u1_struct_0 @ sk_A)))
% 4.34/4.52           | (r3_waybel_9 @ sk_A @ X0 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)))
% 4.34/4.52           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.34/4.52           | ~ (v7_waybel_0 @ X0)
% 4.34/4.52           | ~ (v4_orders_2 @ X0)
% 4.34/4.52           | (v2_struct_0 @ X0)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['292', '293'])).
% 4.34/4.52  thf('295', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('296', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('297', plain,
% 4.34/4.52      ((![X0 : $i, X1 : $i]:
% 4.34/4.52          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52           | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52           | (v1_compts_1 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ sk_A)
% 4.34/4.52           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 4.34/4.52           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 4.34/4.52                (sk_D @ k1_xboole_0 @ 
% 4.34/4.52                 (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52                 (u1_struct_0 @ sk_A)))
% 4.34/4.52           | (r3_waybel_9 @ sk_A @ X0 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)))
% 4.34/4.52           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.34/4.52           | ~ (v7_waybel_0 @ X0)
% 4.34/4.52           | ~ (v4_orders_2 @ X0)
% 4.34/4.52           | (v2_struct_0 @ X0)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['294', '295', '296'])).
% 4.34/4.52  thf('298', plain,
% 4.34/4.52      ((![X0 : $i, X1 : $i]:
% 4.34/4.52          ((v2_struct_0 @ X0)
% 4.34/4.52           | ~ (v4_orders_2 @ X0)
% 4.34/4.52           | ~ (v7_waybel_0 @ X0)
% 4.34/4.52           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.34/4.52           | (r3_waybel_9 @ sk_A @ X0 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)))
% 4.34/4.52           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 4.34/4.52                (sk_D @ k1_xboole_0 @ 
% 4.34/4.52                 (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52                 (u1_struct_0 @ sk_A)))
% 4.34/4.52           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 4.34/4.52           | (v2_struct_0 @ sk_A)
% 4.34/4.52           | (v1_compts_1 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52              k1_xboole_0)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['297'])).
% 4.34/4.52  thf('299', plain,
% 4.34/4.52      ((![X0 : $i]:
% 4.34/4.52          ((v2_struct_0 @ sk_A)
% 4.34/4.52           | (v1_compts_1 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52              k1_xboole_0)
% 4.34/4.52           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52              k1_xboole_0)
% 4.34/4.52           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52           | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52           | (v1_compts_1 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ sk_A)
% 4.34/4.52           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 4.34/4.52           | (r3_waybel_9 @ sk_A @ X0 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)))
% 4.34/4.52           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.34/4.52           | ~ (v7_waybel_0 @ X0)
% 4.34/4.52           | ~ (v4_orders_2 @ X0)
% 4.34/4.52           | (v2_struct_0 @ X0)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['291', '298'])).
% 4.34/4.52  thf('300', plain,
% 4.34/4.52      ((![X0 : $i]:
% 4.34/4.52          ((v2_struct_0 @ X0)
% 4.34/4.52           | ~ (v4_orders_2 @ X0)
% 4.34/4.52           | ~ (v7_waybel_0 @ X0)
% 4.34/4.52           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 4.34/4.52           | (r3_waybel_9 @ sk_A @ X0 @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)))
% 4.34/4.52           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 4.34/4.52           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52              k1_xboole_0)
% 4.34/4.52           | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52           | (v1_compts_1 @ sk_A)
% 4.34/4.52           | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['299'])).
% 4.34/4.52  thf('301', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['252', '300'])).
% 4.34/4.52  thf('302', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['301'])).
% 4.34/4.52  thf('303', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['251', '302'])).
% 4.34/4.52  thf('304', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('305', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('306', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['303', '304', '305'])).
% 4.34/4.52  thf('307', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['306'])).
% 4.34/4.52  thf('308', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['250', '307'])).
% 4.34/4.52  thf('309', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('310', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('311', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['308', '309', '310'])).
% 4.34/4.52  thf('312', plain,
% 4.34/4.52      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['311'])).
% 4.34/4.52  thf('313', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['249', '312'])).
% 4.34/4.52  thf('314', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('315', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('316', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['313', '314', '315'])).
% 4.34/4.52  thf('317', plain,
% 4.34/4.52      ((((r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52          (sk_D @ k1_xboole_0 @ 
% 4.34/4.52           (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52           (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['316'])).
% 4.34/4.52  thf('318', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (m1_subset_1 @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)) @ 
% 4.34/4.52            (u1_struct_0 @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['268', '271'])).
% 4.34/4.52  thf('319', plain,
% 4.34/4.52      (![X33 : $i, X34 : $i]:
% 4.34/4.52         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 4.34/4.52          | ~ (r3_waybel_9 @ X33 @ (sk_B @ X33) @ X34)
% 4.34/4.52          | (v1_compts_1 @ X33)
% 4.34/4.52          | ~ (l1_pre_topc @ X33)
% 4.34/4.52          | ~ (v2_pre_topc @ X33)
% 4.34/4.52          | (v2_struct_0 @ X33))),
% 4.34/4.52      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.52  thf('320', plain,
% 4.34/4.52      ((((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52          k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['318', '319'])).
% 4.34/4.52  thf('321', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('322', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('323', plain,
% 4.34/4.52      ((((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52          k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52              (sk_D @ k1_xboole_0 @ 
% 4.34/4.52               (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52               (u1_struct_0 @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['320', '321', '322'])).
% 4.34/4.52  thf('324', plain,
% 4.34/4.52      (((~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 4.34/4.52            (sk_D @ k1_xboole_0 @ 
% 4.34/4.52             (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52             (u1_struct_0 @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['323'])).
% 4.34/4.52  thf('325', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['317', '324'])).
% 4.34/4.52  thf('326', plain,
% 4.34/4.52      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 4.34/4.52            k1_xboole_0)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['325'])).
% 4.34/4.52  thf('327', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 4.34/4.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.34/4.52  thf(d10_xboole_0, axiom,
% 4.34/4.52    (![A:$i,B:$i]:
% 4.34/4.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.34/4.52  thf('328', plain,
% 4.34/4.52      (![X0 : $i, X2 : $i]:
% 4.34/4.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.34/4.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.34/4.52  thf('329', plain,
% 4.34/4.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.34/4.52      inference('sup-', [status(thm)], ['327', '328'])).
% 4.34/4.52  thf('330', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ((k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) = (k1_xboole_0))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['326', '329'])).
% 4.34/4.52  thf('331', plain,
% 4.34/4.52      (![X19 : $i, X20 : $i]:
% 4.34/4.52         ((v2_struct_0 @ X19)
% 4.34/4.52          | ~ (v4_orders_2 @ X19)
% 4.34/4.52          | ~ (v7_waybel_0 @ X19)
% 4.34/4.52          | ~ (l1_waybel_0 @ X19 @ X20)
% 4.34/4.52          | ~ (v3_yellow_6 @ X19 @ X20)
% 4.34/4.52          | ((k10_yellow_6 @ X20 @ X19) != (k1_xboole_0))
% 4.34/4.52          | ~ (l1_pre_topc @ X20)
% 4.34/4.52          | ~ (v2_pre_topc @ X20)
% 4.34/4.52          | (v2_struct_0 @ X20))),
% 4.34/4.52      inference('cnf', [status(esa)], [d19_yellow_6])).
% 4.34/4.52  thf('332', plain,
% 4.34/4.52      (((((k1_xboole_0) != (k1_xboole_0))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['330', '331'])).
% 4.34/4.52  thf('333', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('334', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('335', plain,
% 4.34/4.52      (((((k1_xboole_0) != (k1_xboole_0))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['332', '333', '334'])).
% 4.34/4.52  thf('336', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['335'])).
% 4.34/4.52  thf('337', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['248', '336'])).
% 4.34/4.52  thf('338', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['337'])).
% 4.34/4.52  thf('339', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['224', '338'])).
% 4.34/4.52  thf('340', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['339'])).
% 4.34/4.52  thf('341', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['206', '340'])).
% 4.34/4.52  thf('342', plain,
% 4.34/4.52      (((~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['341'])).
% 4.34/4.52  thf('343', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['182', '342'])).
% 4.34/4.52  thf('344', plain,
% 4.34/4.52      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['343'])).
% 4.34/4.52  thf('345', plain,
% 4.34/4.52      (![X33 : $i]:
% 4.34/4.52         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 4.34/4.52          | (v1_compts_1 @ X33)
% 4.34/4.52          | ~ (l1_pre_topc @ X33)
% 4.34/4.52          | ~ (v2_pre_topc @ X33)
% 4.34/4.52          | (v2_struct_0 @ X33))),
% 4.34/4.52      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.52  thf('346', plain,
% 4.34/4.52      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['161'])).
% 4.34/4.52  thf('347', plain,
% 4.34/4.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.34/4.52         (~ (l1_struct_0 @ X16)
% 4.34/4.52          | (v2_struct_0 @ X16)
% 4.34/4.52          | (v2_struct_0 @ X17)
% 4.34/4.52          | ~ (v4_orders_2 @ X17)
% 4.34/4.52          | ~ (v7_waybel_0 @ X17)
% 4.34/4.52          | ~ (l1_waybel_0 @ X17 @ X16)
% 4.34/4.52          | ~ (v2_struct_0 @ X18)
% 4.34/4.52          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 4.34/4.52      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 4.34/4.52  thf('348', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (l1_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['346', '347'])).
% 4.34/4.52  thf('349', plain, ((l1_struct_0 @ sk_A)),
% 4.34/4.52      inference('sup-', [status(thm)], ['59', '60'])).
% 4.34/4.52  thf('350', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['348', '349'])).
% 4.34/4.52  thf('351', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 4.34/4.52         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['350'])).
% 4.34/4.52  thf('352', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['345', '351'])).
% 4.34/4.52  thf('353', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('354', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('355', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['352', '353', '354'])).
% 4.34/4.52  thf('356', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['355'])).
% 4.34/4.52  thf('357', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['344', '356'])).
% 4.34/4.52  thf('358', plain,
% 4.34/4.52      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['357'])).
% 4.34/4.52  thf('359', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['141', '358'])).
% 4.34/4.52  thf('360', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('361', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('362', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['359', '360', '361'])).
% 4.34/4.52  thf('363', plain,
% 4.34/4.52      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['362'])).
% 4.34/4.52  thf('364', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['140', '363'])).
% 4.34/4.52  thf('365', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('366', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('367', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['364', '365', '366'])).
% 4.34/4.52  thf('368', plain,
% 4.34/4.52      ((((v2_struct_0 @ (sk_B @ sk_A))
% 4.34/4.52         | (v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['367'])).
% 4.34/4.52  thf('369', plain, (~ (v2_struct_0 @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('370', plain,
% 4.34/4.52      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ (sk_B @ sk_A))))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('clc', [status(thm)], ['368', '369'])).
% 4.34/4.52  thf('371', plain,
% 4.34/4.52      (![X33 : $i]:
% 4.34/4.52         (~ (v2_struct_0 @ (sk_B @ X33))
% 4.34/4.52          | (v1_compts_1 @ X33)
% 4.34/4.52          | ~ (l1_pre_topc @ X33)
% 4.34/4.52          | ~ (v2_pre_topc @ X33)
% 4.34/4.52          | (v2_struct_0 @ X33))),
% 4.34/4.52      inference('cnf', [status(esa)], [t36_yellow19])).
% 4.34/4.52  thf('372', plain,
% 4.34/4.52      ((((v1_compts_1 @ sk_A)
% 4.34/4.52         | (v2_struct_0 @ sk_A)
% 4.34/4.52         | ~ (v2_pre_topc @ sk_A)
% 4.34/4.52         | ~ (l1_pre_topc @ sk_A)
% 4.34/4.52         | (v1_compts_1 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('sup-', [status(thm)], ['370', '371'])).
% 4.34/4.52  thf('373', plain, ((v2_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('374', plain, ((l1_pre_topc @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('375', plain,
% 4.34/4.52      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('demod', [status(thm)], ['372', '373', '374'])).
% 4.34/4.52  thf('376', plain,
% 4.34/4.52      ((((v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('simplify', [status(thm)], ['375'])).
% 4.34/4.52  thf('377', plain, (~ (v2_struct_0 @ sk_A)),
% 4.34/4.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.34/4.52  thf('378', plain,
% 4.34/4.52      (((v1_compts_1 @ sk_A))
% 4.34/4.52         <= ((![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) & 
% 4.34/4.52             (![X37 : $i]:
% 4.34/4.52                ((v2_struct_0 @ X37)
% 4.34/4.52                 | ~ (v4_orders_2 @ X37)
% 4.34/4.52                 | ~ (v7_waybel_0 @ X37)
% 4.34/4.52                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52                 | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37))))),
% 4.34/4.52      inference('clc', [status(thm)], ['376', '377'])).
% 4.34/4.52  thf('379', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 4.34/4.52      inference('split', [status(esa)], ['2'])).
% 4.34/4.52  thf('380', plain,
% 4.34/4.52      (~
% 4.34/4.52       (![X37 : $i]:
% 4.34/4.52          ((v2_struct_0 @ X37)
% 4.34/4.52           | ~ (v4_orders_2 @ X37)
% 4.34/4.52           | ~ (v7_waybel_0 @ X37)
% 4.34/4.52           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52           | (v3_yellow_6 @ (sk_C_2 @ X37) @ sk_A))) | 
% 4.34/4.52       ((v1_compts_1 @ sk_A)) | 
% 4.34/4.52       ~
% 4.34/4.52       (![X37 : $i]:
% 4.34/4.52          ((v2_struct_0 @ X37)
% 4.34/4.52           | ~ (v4_orders_2 @ X37)
% 4.34/4.52           | ~ (v7_waybel_0 @ X37)
% 4.34/4.52           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 4.34/4.52           | (m2_yellow_6 @ (sk_C_2 @ X37) @ sk_A @ X37)))),
% 4.34/4.52      inference('sup-', [status(thm)], ['378', '379'])).
% 4.34/4.52  thf('381', plain, ($false),
% 4.34/4.52      inference('sat_resolution*', [status(thm)],
% 4.34/4.52                ['1', '3', '5', '7', '9', '11', '138', '139', '380'])).
% 4.34/4.52  
% 4.34/4.52  % SZS output end Refutation
% 4.34/4.52  
% 4.34/4.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
