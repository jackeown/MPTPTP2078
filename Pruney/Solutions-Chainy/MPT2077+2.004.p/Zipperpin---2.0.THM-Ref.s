%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mBBRxkZlhR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:57 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  417 (2318 expanded)
%              Number of leaves         :   39 ( 623 expanded)
%              Depth                    :   83
%              Number of atoms          : 8506 (47244 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

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
    ! [X35: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( l1_waybel_0 @ X35 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X34: $i] :
      ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
      | ~ ( v3_yellow_6 @ X34 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X34: $i] :
        ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
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
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('13',plain,(
    ! [X35: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( l1_waybel_0 @ X35 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('16',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(t35_yellow19,axiom,(
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
                ( ( r3_waybel_9 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X31: $i,X33: $i] :
      ( ~ ( v1_compts_1 @ X31 )
      | ( r3_waybel_9 @ X31 @ X33 @ ( sk_C_1 @ X33 @ X31 ) )
      | ~ ( l1_waybel_0 @ X33 @ X31 )
      | ~ ( v7_waybel_0 @ X33 )
      | ~ ( v4_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('18',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
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
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
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
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('28',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('30',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,(
    ! [X31: $i,X33: $i] :
      ( ~ ( v1_compts_1 @ X31 )
      | ( m1_subset_1 @ ( sk_C_1 @ X33 @ X31 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_waybel_0 @ X33 @ X31 )
      | ~ ( v7_waybel_0 @ X33 )
      | ~ ( v4_orders_2 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
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
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
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
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
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
    ( ! [X34: $i] :
        ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
   <= ! [X34: $i] :
        ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X34 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
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
   <= ( ! [X34: $i] :
          ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ! [X34: $i] :
          ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
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
   <= ( ! [X34: $i] :
          ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
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
   <= ( ! [X34: $i] :
          ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
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
    | ~ ! [X34: $i] :
          ( ~ ( m2_yellow_6 @ X34 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X34 @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('140',plain,(
    ! [X31: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('141',plain,(
    ! [X31: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('142',plain,(
    ! [X31: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('143',plain,(
    ! [X31: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('144',plain,(
    ! [X31: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X31 ) @ X31 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('145',plain,(
    ! [X31: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('146',plain,(
    ! [X31: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('147',plain,(
    ! [X31: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X31 ) @ X31 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('148',plain,
    ( ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X31: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('184',plain,(
    ! [X31: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('185',plain,(
    ! [X31: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X31 ) @ X31 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('186',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X31: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('208',plain,(
    ! [X31: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('209',plain,(
    ! [X31: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X31 ) @ X31 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('210',plain,
    ( ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X31: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('226',plain,(
    ! [X31: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('227',plain,(
    ! [X31: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X31 ) @ X31 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('228',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X31: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('250',plain,(
    ! [X31: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('251',plain,(
    ! [X31: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X31 ) @ X31 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('252',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('253',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('254',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('255',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('258',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('259',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['261','262','263'])).

thf('265',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['258','265'])).

thf('267',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['257','267'])).

thf('269',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['255','280'])).

thf('282',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['254','282'])).

thf('284',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['253','284'])).

thf('286',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m2_yellow_6 @ X2 @ sk_A @ X1 )
        | ~ ( r3_waybel_9 @ sk_A @ X2 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ( v2_struct_0 @ X1 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m2_yellow_6 @ X2 @ sk_A @ X1 )
        | ~ ( r3_waybel_9 @ sk_A @ X2 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ( v2_struct_0 @ X1 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['289','290','291'])).

thf('293',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v2_struct_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( r3_waybel_9 @ sk_A @ X2 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( m2_yellow_6 @ X2 @ sk_A @ X1 )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ~ ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ X1 )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ( v2_struct_0 @ X1 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['286','293'])).

thf('295',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X1 )
        | ~ ( v4_orders_2 @ X1 )
        | ~ ( v7_waybel_0 @ X1 )
        | ~ ( l1_waybel_0 @ X1 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ X1 )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['252','295'])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['303','304','305'])).

thf('307',plain,
    ( ! [X0: $i] :
        ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['308','309','310'])).

thf('312',plain,
    ( ! [X0: $i] :
        ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( m1_subset_1 @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['256','271'])).

thf('314',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( r3_waybel_9 @ X31 @ ( sk_B @ X31 ) @ X32 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('315',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['315','316','317'])).

thf('319',plain,
    ( ! [X0: $i] :
        ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['312','319'])).

thf('321',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ X0 )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['327','328','329'])).

thf('331',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['248','331'])).

thf('333',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['224','333'])).

thf('335',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['206','335'])).

thf('337',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['182','337'])).

thf('339',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['338'])).

thf('340',plain,(
    ! [X31: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X31 ) @ X31 )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('341',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['343','344'])).

thf('346',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['345'])).

thf('347',plain,
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
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['347','348','349'])).

thf('351',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X35: $i] :
        ( ( v2_struct_0 @ X35 )
        | ~ ( v4_orders_2 @ X35 )
        | ~ ( v7_waybel_0 @ X35 )
        | ~ ( l1_waybel_0 @ X35 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
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
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['339','351'])).

thf('353',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
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
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
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
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['354','355','356'])).

thf('358',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['357'])).

thf('359',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
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
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['359','360','361'])).

thf('363',plain,
    ( ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['362'])).

thf('364',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['363','364'])).

thf('366',plain,(
    ! [X31: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X31 ) )
      | ( v1_compts_1 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('367',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
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
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['367','368','369'])).

thf('371',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('373',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
      & ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['371','372'])).

thf('374',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('375',plain,
    ( ~ ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ~ ! [X35: $i] :
          ( ( v2_struct_0 @ X35 )
          | ~ ( v4_orders_2 @ X35 )
          | ~ ( v7_waybel_0 @ X35 )
          | ~ ( l1_waybel_0 @ X35 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['373','374'])).

thf('376',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','138','139','375'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mBBRxkZlhR
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.35/2.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.35/2.58  % Solved by: fo/fo7.sh
% 2.35/2.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.35/2.58  % done 1808 iterations in 2.113s
% 2.35/2.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.35/2.58  % SZS output start Refutation
% 2.35/2.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.35/2.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.35/2.58  thf(sk_B_type, type, sk_B: $i > $i).
% 2.35/2.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.35/2.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.35/2.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.35/2.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.35/2.58  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 2.35/2.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.35/2.58  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 2.35/2.58  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 2.35/2.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.35/2.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.35/2.58  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 2.35/2.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.35/2.58  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 2.35/2.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.35/2.58  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 2.35/2.58  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 2.35/2.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.35/2.58  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 2.35/2.58  thf(sk_A_type, type, sk_A: $i).
% 2.35/2.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.35/2.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.35/2.58  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 2.35/2.58  thf(t37_yellow19, conjecture,
% 2.35/2.58    (![A:$i]:
% 2.35/2.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.35/2.58       ( ( v1_compts_1 @ A ) <=>
% 2.35/2.58         ( ![B:$i]:
% 2.35/2.58           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.58               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.58             ( ?[C:$i]:
% 2.35/2.58               ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ))).
% 2.35/2.58  thf(zf_stmt_0, negated_conjecture,
% 2.35/2.58    (~( ![A:$i]:
% 2.35/2.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.35/2.58            ( l1_pre_topc @ A ) ) =>
% 2.35/2.58          ( ( v1_compts_1 @ A ) <=>
% 2.35/2.58            ( ![B:$i]:
% 2.35/2.58              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.58                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.58                ( ?[C:$i]:
% 2.35/2.58                  ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ) )),
% 2.35/2.58    inference('cnf.neg', [status(esa)], [t37_yellow19])).
% 2.35/2.58  thf('0', plain,
% 2.35/2.58      (![X35 : $i]:
% 2.35/2.58         ((v2_struct_0 @ X35)
% 2.35/2.58          | ~ (v4_orders_2 @ X35)
% 2.35/2.58          | ~ (v7_waybel_0 @ X35)
% 2.35/2.58          | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.58          | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35)
% 2.35/2.58          | (v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('1', plain,
% 2.35/2.58      ((![X35 : $i]:
% 2.35/2.58          ((v2_struct_0 @ X35)
% 2.35/2.58           | ~ (v4_orders_2 @ X35)
% 2.35/2.58           | ~ (v7_waybel_0 @ X35)
% 2.35/2.58           | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.58           | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))) | 
% 2.35/2.58       ((v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('split', [status(esa)], ['0'])).
% 2.35/2.58  thf('2', plain,
% 2.35/2.58      (![X34 : $i]:
% 2.35/2.58         (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1)
% 2.35/2.58          | ~ (v3_yellow_6 @ X34 @ sk_A)
% 2.35/2.58          | ~ (v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('3', plain,
% 2.35/2.58      ((![X34 : $i]:
% 2.35/2.58          (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X34 @ sk_A))) | 
% 2.35/2.58       ~ ((v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('split', [status(esa)], ['2'])).
% 2.35/2.58  thf('4', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('5', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('split', [status(esa)], ['4'])).
% 2.35/2.58  thf('6', plain, (((v7_waybel_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('7', plain, (((v7_waybel_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('split', [status(esa)], ['6'])).
% 2.35/2.58  thf('8', plain, (((v4_orders_2 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('9', plain, (((v4_orders_2 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('split', [status(esa)], ['8'])).
% 2.35/2.58  thf('10', plain, ((~ (v2_struct_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('11', plain, (~ ((v2_struct_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('split', [status(esa)], ['10'])).
% 2.35/2.58  thf('12', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['6'])).
% 2.35/2.58  thf('13', plain,
% 2.35/2.58      (![X35 : $i]:
% 2.35/2.58         ((v2_struct_0 @ X35)
% 2.35/2.58          | ~ (v4_orders_2 @ X35)
% 2.35/2.58          | ~ (v7_waybel_0 @ X35)
% 2.35/2.58          | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.58          | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A)
% 2.35/2.58          | (v1_compts_1 @ sk_A))),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('14', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['13'])).
% 2.35/2.58  thf('15', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['8'])).
% 2.35/2.58  thf('16', plain,
% 2.35/2.58      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['4'])).
% 2.35/2.58  thf(t35_yellow19, axiom,
% 2.35/2.58    (![A:$i]:
% 2.35/2.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.35/2.58       ( ( v1_compts_1 @ A ) <=>
% 2.35/2.58         ( ![B:$i]:
% 2.35/2.58           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.58               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.58             ( ?[C:$i]:
% 2.35/2.58               ( ( r3_waybel_9 @ A @ B @ C ) & 
% 2.35/2.58                 ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 2.35/2.58  thf('17', plain,
% 2.35/2.58      (![X31 : $i, X33 : $i]:
% 2.35/2.58         (~ (v1_compts_1 @ X31)
% 2.35/2.58          | (r3_waybel_9 @ X31 @ X33 @ (sk_C_1 @ X33 @ X31))
% 2.35/2.58          | ~ (l1_waybel_0 @ X33 @ X31)
% 2.35/2.58          | ~ (v7_waybel_0 @ X33)
% 2.35/2.58          | ~ (v4_orders_2 @ X33)
% 2.35/2.58          | (v2_struct_0 @ X33)
% 2.35/2.58          | ~ (l1_pre_topc @ X31)
% 2.35/2.58          | ~ (v2_pre_topc @ X31)
% 2.35/2.58          | (v2_struct_0 @ X31))),
% 2.35/2.58      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.58  thf('18', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.58         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['16', '17'])).
% 2.35/2.58  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('21', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.35/2.58  thf('22', plain,
% 2.35/2.58      (((~ (v1_compts_1 @ sk_A)
% 2.35/2.58         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['15', '21'])).
% 2.35/2.58  thf('23', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['14', '22'])).
% 2.35/2.58  thf('24', plain,
% 2.35/2.58      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['12', '23'])).
% 2.35/2.58  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('26', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['24', '25'])).
% 2.35/2.58  thf('27', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['6'])).
% 2.35/2.58  thf('28', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['13'])).
% 2.35/2.58  thf('29', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['8'])).
% 2.35/2.58  thf('30', plain,
% 2.35/2.58      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['4'])).
% 2.35/2.58  thf('31', plain,
% 2.35/2.58      (![X31 : $i, X33 : $i]:
% 2.35/2.58         (~ (v1_compts_1 @ X31)
% 2.35/2.58          | (m1_subset_1 @ (sk_C_1 @ X33 @ X31) @ (u1_struct_0 @ X31))
% 2.35/2.58          | ~ (l1_waybel_0 @ X33 @ X31)
% 2.35/2.58          | ~ (v7_waybel_0 @ X33)
% 2.35/2.58          | ~ (v4_orders_2 @ X33)
% 2.35/2.58          | (v2_struct_0 @ X33)
% 2.35/2.58          | ~ (l1_pre_topc @ X31)
% 2.35/2.58          | ~ (v2_pre_topc @ X31)
% 2.35/2.58          | (v2_struct_0 @ X31))),
% 2.35/2.58      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.58  thf('32', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.58         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.35/2.58         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['30', '31'])).
% 2.35/2.58  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('35', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.35/2.58         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.35/2.58  thf('36', plain,
% 2.35/2.58      (((~ (v1_compts_1 @ sk_A)
% 2.35/2.58         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['29', '35'])).
% 2.35/2.58  thf('37', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['28', '36'])).
% 2.35/2.58  thf('38', plain,
% 2.35/2.58      ((((m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['27', '37'])).
% 2.35/2.58  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('40', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['38', '39'])).
% 2.35/2.58  thf(t32_waybel_9, axiom,
% 2.35/2.58    (![A:$i]:
% 2.35/2.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.35/2.58       ( ![B:$i]:
% 2.35/2.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.58           ( ![C:$i]:
% 2.35/2.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.35/2.58               ( ~( ( r3_waybel_9 @ A @ B @ C ) & 
% 2.35/2.58                    ( ![D:$i]:
% 2.35/2.58                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 2.35/2.58                        ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.35/2.58  thf('41', plain,
% 2.35/2.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.35/2.58         ((v2_struct_0 @ X28)
% 2.35/2.58          | ~ (v4_orders_2 @ X28)
% 2.35/2.58          | ~ (v7_waybel_0 @ X28)
% 2.35/2.58          | ~ (l1_waybel_0 @ X28 @ X29)
% 2.35/2.58          | (m2_yellow_6 @ (sk_D @ X30 @ X28 @ X29) @ X29 @ X28)
% 2.35/2.58          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 2.35/2.58          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 2.35/2.58          | ~ (l1_pre_topc @ X29)
% 2.35/2.58          | ~ (v2_pre_topc @ X29)
% 2.35/2.58          | (v2_struct_0 @ X29))),
% 2.35/2.58      inference('cnf', [status(esa)], [t32_waybel_9])).
% 2.35/2.58  thf('42', plain,
% 2.35/2.58      ((![X0 : $i]:
% 2.35/2.58          ((v2_struct_0 @ sk_B_1)
% 2.35/2.58           | (v2_struct_0 @ sk_A)
% 2.35/2.58           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.58           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.58           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.58           | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 2.35/2.58              sk_A @ X0)
% 2.35/2.58           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.35/2.58           | ~ (v7_waybel_0 @ X0)
% 2.35/2.58           | ~ (v4_orders_2 @ X0)
% 2.35/2.58           | (v2_struct_0 @ X0)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['40', '41'])).
% 2.35/2.58  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('45', plain,
% 2.35/2.58      ((![X0 : $i]:
% 2.35/2.58          ((v2_struct_0 @ sk_B_1)
% 2.35/2.58           | (v2_struct_0 @ sk_A)
% 2.35/2.58           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.58           | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 2.35/2.58              sk_A @ X0)
% 2.35/2.58           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.35/2.58           | ~ (v7_waybel_0 @ X0)
% 2.35/2.58           | ~ (v4_orders_2 @ X0)
% 2.35/2.58           | (v2_struct_0 @ X0)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('demod', [status(thm)], ['42', '43', '44'])).
% 2.35/2.58  thf('46', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 2.35/2.58         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['26', '45'])).
% 2.35/2.58  thf('47', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['8'])).
% 2.35/2.58  thf('48', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['6'])).
% 2.35/2.58  thf('49', plain,
% 2.35/2.58      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['4'])).
% 2.35/2.58  thf('50', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 2.35/2.58  thf('51', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('simplify', [status(thm)], ['50'])).
% 2.35/2.58  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('53', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['51', '52'])).
% 2.35/2.58  thf(dt_m2_yellow_6, axiom,
% 2.35/2.58    (![A:$i,B:$i]:
% 2.35/2.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 2.35/2.58         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.58         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.58       ( ![C:$i]:
% 2.35/2.58         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 2.35/2.58           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 2.35/2.58             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 2.35/2.58  thf('54', plain,
% 2.35/2.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.58         (~ (l1_struct_0 @ X16)
% 2.35/2.58          | (v2_struct_0 @ X16)
% 2.35/2.58          | (v2_struct_0 @ X17)
% 2.35/2.58          | ~ (v4_orders_2 @ X17)
% 2.35/2.58          | ~ (v7_waybel_0 @ X17)
% 2.35/2.58          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.58          | (v4_orders_2 @ X18)
% 2.35/2.58          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.58      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.58  thf('55', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['53', '54'])).
% 2.35/2.58  thf('56', plain,
% 2.35/2.58      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['4'])).
% 2.35/2.58  thf('57', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['6'])).
% 2.35/2.58  thf('58', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['8'])).
% 2.35/2.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf(dt_l1_pre_topc, axiom,
% 2.35/2.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.35/2.58  thf('60', plain,
% 2.35/2.58      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 2.35/2.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.35/2.58  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.58      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.58  thf('62', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('demod', [status(thm)], ['55', '56', '57', '58', '61'])).
% 2.35/2.58  thf('63', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('simplify', [status(thm)], ['62'])).
% 2.35/2.58  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('65', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['63', '64'])).
% 2.35/2.58  thf('66', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['51', '52'])).
% 2.35/2.58  thf('67', plain,
% 2.35/2.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.58         (~ (l1_struct_0 @ X16)
% 2.35/2.58          | (v2_struct_0 @ X16)
% 2.35/2.58          | (v2_struct_0 @ X17)
% 2.35/2.58          | ~ (v4_orders_2 @ X17)
% 2.35/2.58          | ~ (v7_waybel_0 @ X17)
% 2.35/2.58          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.58          | (v7_waybel_0 @ X18)
% 2.35/2.58          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.58      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.58  thf('68', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['66', '67'])).
% 2.35/2.58  thf('69', plain,
% 2.35/2.58      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['4'])).
% 2.35/2.58  thf('70', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['6'])).
% 2.35/2.58  thf('71', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['8'])).
% 2.35/2.58  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.58      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.58  thf('73', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 2.35/2.58  thf('74', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('simplify', [status(thm)], ['73'])).
% 2.35/2.58  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('76', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['74', '75'])).
% 2.35/2.58  thf('77', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['51', '52'])).
% 2.35/2.58  thf('78', plain,
% 2.35/2.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.58         (~ (l1_struct_0 @ X16)
% 2.35/2.58          | (v2_struct_0 @ X16)
% 2.35/2.58          | (v2_struct_0 @ X17)
% 2.35/2.58          | ~ (v4_orders_2 @ X17)
% 2.35/2.58          | ~ (v7_waybel_0 @ X17)
% 2.35/2.58          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.58          | (l1_waybel_0 @ X18 @ X16)
% 2.35/2.58          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.58      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.58  thf('79', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 2.35/2.58         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.58         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['77', '78'])).
% 2.35/2.58  thf('80', plain,
% 2.35/2.58      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.58      inference('split', [status(esa)], ['4'])).
% 2.35/2.58  thf('81', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['6'])).
% 2.35/2.58  thf('82', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('split', [status(esa)], ['8'])).
% 2.35/2.58  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.58      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.58  thf('84', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 2.35/2.58  thf('85', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('simplify', [status(thm)], ['84'])).
% 2.35/2.58  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('87', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (l1_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['85', '86'])).
% 2.35/2.58  thf(d19_yellow_6, axiom,
% 2.35/2.58    (![A:$i]:
% 2.35/2.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.35/2.58       ( ![B:$i]:
% 2.35/2.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.58             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.58           ( ( v3_yellow_6 @ B @ A ) <=>
% 2.35/2.58             ( ( k10_yellow_6 @ A @ B ) != ( k1_xboole_0 ) ) ) ) ) ))).
% 2.35/2.58  thf('88', plain,
% 2.35/2.58      (![X19 : $i, X20 : $i]:
% 2.35/2.58         ((v2_struct_0 @ X19)
% 2.35/2.58          | ~ (v4_orders_2 @ X19)
% 2.35/2.58          | ~ (v7_waybel_0 @ X19)
% 2.35/2.58          | ~ (l1_waybel_0 @ X19 @ X20)
% 2.35/2.58          | ((k10_yellow_6 @ X20 @ X19) = (k1_xboole_0))
% 2.35/2.58          | (v3_yellow_6 @ X19 @ X20)
% 2.35/2.58          | ~ (l1_pre_topc @ X20)
% 2.35/2.58          | ~ (v2_pre_topc @ X20)
% 2.35/2.58          | (v2_struct_0 @ X20))),
% 2.35/2.58      inference('cnf', [status(esa)], [d19_yellow_6])).
% 2.35/2.58  thf('89', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.58         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.58         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | ((k10_yellow_6 @ sk_A @ 
% 2.35/2.58             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 2.35/2.58         | ~ (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['87', '88'])).
% 2.35/2.58  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.58  thf('92', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | ((k10_yellow_6 @ sk_A @ 
% 2.35/2.58             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 2.35/2.58         | ~ (v7_waybel_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('demod', [status(thm)], ['89', '90', '91'])).
% 2.35/2.58  thf('93', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | ((k10_yellow_6 @ sk_A @ 
% 2.35/2.58             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 2.35/2.58         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['76', '92'])).
% 2.35/2.58  thf('94', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | ((k10_yellow_6 @ sk_A @ 
% 2.35/2.58             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 2.35/2.58         | ~ (v4_orders_2 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('simplify', [status(thm)], ['93'])).
% 2.35/2.58  thf('95', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | ((k10_yellow_6 @ sk_A @ 
% 2.35/2.58             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 2.35/2.58         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | (v2_struct_0 @ sk_A)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('sup-', [status(thm)], ['65', '94'])).
% 2.35/2.58  thf('96', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_A)
% 2.35/2.58         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.58            sk_A)
% 2.35/2.58         | ((k10_yellow_6 @ sk_A @ 
% 2.35/2.58             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 2.35/2.58         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.58         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('simplify', [status(thm)], ['95'])).
% 2.35/2.58  thf('97', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['24', '25'])).
% 2.35/2.58  thf('98', plain,
% 2.35/2.58      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.58         | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.58             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.58             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.58             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.58      inference('clc', [status(thm)], ['38', '39'])).
% 2.35/2.58  thf('99', plain,
% 2.35/2.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.35/2.58         ((v2_struct_0 @ X28)
% 2.35/2.58          | ~ (v4_orders_2 @ X28)
% 2.35/2.58          | ~ (v7_waybel_0 @ X28)
% 2.35/2.58          | ~ (l1_waybel_0 @ X28 @ X29)
% 2.35/2.58          | (r2_hidden @ X30 @ (k10_yellow_6 @ X29 @ (sk_D @ X30 @ X28 @ X29)))
% 2.35/2.58          | ~ (r3_waybel_9 @ X29 @ X28 @ X30)
% 2.35/2.58          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 2.35/2.58          | ~ (l1_pre_topc @ X29)
% 2.35/2.58          | ~ (v2_pre_topc @ X29)
% 2.35/2.58          | (v2_struct_0 @ X29))),
% 2.35/2.58      inference('cnf', [status(esa)], [t32_waybel_9])).
% 2.35/2.58  thf('100', plain,
% 2.35/2.58      ((![X0 : $i]:
% 2.35/2.58          ((v2_struct_0 @ sk_B_1)
% 2.35/2.58           | (v2_struct_0 @ sk_A)
% 2.35/2.58           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.58           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.58           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.58           | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 2.35/2.58              (k10_yellow_6 @ sk_A @ 
% 2.35/2.58               (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 2.35/2.58           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.35/2.58           | ~ (v7_waybel_0 @ X0)
% 2.35/2.58           | ~ (v4_orders_2 @ X0)
% 2.35/2.58           | (v2_struct_0 @ X0)))
% 2.35/2.58         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['98', '99'])).
% 2.35/2.59  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('103', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_B_1)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.59           | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 2.35/2.59              (k10_yellow_6 @ sk_A @ 
% 2.35/2.59               (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 2.35/2.59           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 2.35/2.59           | ~ (v7_waybel_0 @ X0)
% 2.35/2.59           | ~ (v4_orders_2 @ X0)
% 2.35/2.59           | (v2_struct_0 @ X0)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('demod', [status(thm)], ['100', '101', '102'])).
% 2.35/2.59  thf('104', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)
% 2.35/2.59         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.59         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.59         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 2.35/2.59         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            (k10_yellow_6 @ sk_A @ 
% 2.35/2.59             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['97', '103'])).
% 2.35/2.59  thf('105', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('split', [status(esa)], ['8'])).
% 2.35/2.59  thf('106', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.59      inference('split', [status(esa)], ['6'])).
% 2.35/2.59  thf('107', plain,
% 2.35/2.59      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.59      inference('split', [status(esa)], ['4'])).
% 2.35/2.59  thf('108', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            (k10_yellow_6 @ sk_A @ 
% 2.35/2.59             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 2.35/2.59  thf('109', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            (k10_yellow_6 @ sk_A @ 
% 2.35/2.59             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('simplify', [status(thm)], ['108'])).
% 2.35/2.59  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('111', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            (k10_yellow_6 @ sk_A @ 
% 2.35/2.59             (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('clc', [status(thm)], ['109', '110'])).
% 2.35/2.59  thf(t7_ordinal1, axiom,
% 2.35/2.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.35/2.59  thf('112', plain,
% 2.35/2.59      (![X11 : $i, X12 : $i]:
% 2.35/2.59         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 2.35/2.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.35/2.59  thf('113', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | ~ (r1_tarski @ 
% 2.35/2.59              (k10_yellow_6 @ sk_A @ 
% 2.35/2.59               (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) @ 
% 2.35/2.59              (sk_C_1 @ sk_B_1 @ sk_A))))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['111', '112'])).
% 2.35/2.59  thf('114', plain,
% 2.35/2.59      (((~ (r1_tarski @ k1_xboole_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['96', '113'])).
% 2.35/2.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.35/2.59  thf('115', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 2.35/2.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.35/2.59  thf('116', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('demod', [status(thm)], ['114', '115'])).
% 2.35/2.59  thf('117', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v3_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('simplify', [status(thm)], ['116'])).
% 2.35/2.59  thf('118', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            sk_A @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('clc', [status(thm)], ['51', '52'])).
% 2.35/2.59  thf('119', plain,
% 2.35/2.59      ((![X34 : $i]:
% 2.35/2.59          (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X34 @ sk_A)))
% 2.35/2.59         <= ((![X34 : $i]:
% 2.35/2.59                (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1)
% 2.35/2.59                 | ~ (v3_yellow_6 @ X34 @ sk_A))))),
% 2.35/2.59      inference('split', [status(esa)], ['2'])).
% 2.35/2.59  thf('120', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | ~ (v3_yellow_6 @ 
% 2.35/2.59              (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ sk_A)))
% 2.35/2.59         <= ((![X34 : $i]:
% 2.35/2.59                (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1)
% 2.35/2.59                 | ~ (v3_yellow_6 @ X34 @ sk_A))) & 
% 2.35/2.59             ((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['118', '119'])).
% 2.35/2.59  thf('121', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= ((![X34 : $i]:
% 2.35/2.59                (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1)
% 2.35/2.59                 | ~ (v3_yellow_6 @ X34 @ sk_A))) & 
% 2.35/2.59             ((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['117', '120'])).
% 2.35/2.59  thf('122', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= ((![X34 : $i]:
% 2.35/2.59                (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1)
% 2.35/2.59                 | ~ (v3_yellow_6 @ X34 @ sk_A))) & 
% 2.35/2.59             ((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('simplify', [status(thm)], ['121'])).
% 2.35/2.59  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('124', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 2.35/2.59         <= ((![X34 : $i]:
% 2.35/2.59                (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1)
% 2.35/2.59                 | ~ (v3_yellow_6 @ X34 @ sk_A))) & 
% 2.35/2.59             ((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('clc', [status(thm)], ['122', '123'])).
% 2.35/2.59  thf('125', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (m2_yellow_6 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 2.35/2.59            sk_A @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('clc', [status(thm)], ['51', '52'])).
% 2.35/2.59  thf('126', plain,
% 2.35/2.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.59         (~ (l1_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X17)
% 2.35/2.59          | ~ (v4_orders_2 @ X17)
% 2.35/2.59          | ~ (v7_waybel_0 @ X17)
% 2.35/2.59          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.59          | ~ (v2_struct_0 @ X18)
% 2.35/2.59          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.59      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.59  thf('127', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ sk_B_1)
% 2.35/2.59         | ~ (v4_orders_2 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['125', '126'])).
% 2.35/2.59  thf('128', plain,
% 2.35/2.59      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 2.35/2.59      inference('split', [status(esa)], ['4'])).
% 2.35/2.59  thf('129', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 2.35/2.59      inference('split', [status(esa)], ['6'])).
% 2.35/2.59  thf('130', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('split', [status(esa)], ['8'])).
% 2.35/2.59  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.59      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.59  thf('132', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 2.35/2.59  thf('133', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_B_1)))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('simplify', [status(thm)], ['132'])).
% 2.35/2.59  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('135', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_B_1)
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_D @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 2.35/2.59         <= (((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('clc', [status(thm)], ['133', '134'])).
% 2.35/2.59  thf('136', plain,
% 2.35/2.59      (((v2_struct_0 @ sk_B_1))
% 2.35/2.59         <= ((![X34 : $i]:
% 2.35/2.59                (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1)
% 2.35/2.59                 | ~ (v3_yellow_6 @ X34 @ sk_A))) & 
% 2.35/2.59             ((v1_compts_1 @ sk_A)) & 
% 2.35/2.59             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 2.35/2.59             ((v7_waybel_0 @ sk_B_1)) & 
% 2.35/2.59             ((v4_orders_2 @ sk_B_1)))),
% 2.35/2.59      inference('clc', [status(thm)], ['124', '135'])).
% 2.35/2.59  thf('137', plain,
% 2.35/2.59      ((~ (v2_struct_0 @ sk_B_1)) <= (~ ((v2_struct_0 @ sk_B_1)))),
% 2.35/2.59      inference('split', [status(esa)], ['10'])).
% 2.35/2.59  thf('138', plain,
% 2.35/2.59      (~ ((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A)) | 
% 2.35/2.59       ~
% 2.35/2.59       (![X34 : $i]:
% 2.35/2.59          (~ (m2_yellow_6 @ X34 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X34 @ sk_A))) | 
% 2.35/2.59       ~ ((v7_waybel_0 @ sk_B_1)) | ~ ((v4_orders_2 @ sk_B_1)) | 
% 2.35/2.59       ((v2_struct_0 @ sk_B_1))),
% 2.35/2.59      inference('sup-', [status(thm)], ['136', '137'])).
% 2.35/2.59  thf('139', plain,
% 2.35/2.59      ((![X35 : $i]:
% 2.35/2.59          ((v2_struct_0 @ X35)
% 2.35/2.59           | ~ (v4_orders_2 @ X35)
% 2.35/2.59           | ~ (v7_waybel_0 @ X35)
% 2.35/2.59           | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59           | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) | 
% 2.35/2.59       ((v1_compts_1 @ sk_A))),
% 2.35/2.59      inference('split', [status(esa)], ['13'])).
% 2.35/2.59  thf('140', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v7_waybel_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('141', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v4_orders_2 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('142', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v7_waybel_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('143', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v4_orders_2 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('144', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((l1_waybel_0 @ (sk_B @ X31) @ X31)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('145', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v4_orders_2 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('146', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v7_waybel_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('147', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((l1_waybel_0 @ (sk_B @ X31) @ X31)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('148', plain,
% 2.35/2.59      ((![X35 : $i]:
% 2.35/2.59          ((v2_struct_0 @ X35)
% 2.35/2.59           | ~ (v4_orders_2 @ X35)
% 2.35/2.59           | ~ (v7_waybel_0 @ X35)
% 2.35/2.59           | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59           | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('split', [status(esa)], ['0'])).
% 2.35/2.59  thf('149', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['147', '148'])).
% 2.35/2.59  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('152', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['149', '150', '151'])).
% 2.35/2.59  thf('153', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['146', '152'])).
% 2.35/2.59  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('156', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['153', '154', '155'])).
% 2.35/2.59  thf('157', plain,
% 2.35/2.59      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['156'])).
% 2.35/2.59  thf('158', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['145', '157'])).
% 2.35/2.59  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('161', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['158', '159', '160'])).
% 2.35/2.59  thf('162', plain,
% 2.35/2.59      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['161'])).
% 2.35/2.59  thf('163', plain,
% 2.35/2.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.59         (~ (l1_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X17)
% 2.35/2.59          | ~ (v4_orders_2 @ X17)
% 2.35/2.59          | ~ (v7_waybel_0 @ X17)
% 2.35/2.59          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.59          | (v7_waybel_0 @ X18)
% 2.35/2.59          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.59      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.59  thf('164', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['162', '163'])).
% 2.35/2.59  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.59      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.59  thf('166', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['164', '165'])).
% 2.35/2.59  thf('167', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['166'])).
% 2.35/2.59  thf('168', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['144', '167'])).
% 2.35/2.59  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('171', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['168', '169', '170'])).
% 2.35/2.59  thf('172', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['171'])).
% 2.35/2.59  thf('173', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['143', '172'])).
% 2.35/2.59  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('176', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['173', '174', '175'])).
% 2.35/2.59  thf('177', plain,
% 2.35/2.59      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['176'])).
% 2.35/2.59  thf('178', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['142', '177'])).
% 2.35/2.59  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('181', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['178', '179', '180'])).
% 2.35/2.59  thf('182', plain,
% 2.35/2.59      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['181'])).
% 2.35/2.59  thf('183', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v4_orders_2 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('184', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v7_waybel_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('185', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((l1_waybel_0 @ (sk_B @ X31) @ X31)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('186', plain,
% 2.35/2.59      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['161'])).
% 2.35/2.59  thf('187', plain,
% 2.35/2.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.59         (~ (l1_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X17)
% 2.35/2.59          | ~ (v4_orders_2 @ X17)
% 2.35/2.59          | ~ (v7_waybel_0 @ X17)
% 2.35/2.59          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.59          | (v4_orders_2 @ X18)
% 2.35/2.59          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.59      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.59  thf('188', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['186', '187'])).
% 2.35/2.59  thf('189', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.59      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.59  thf('190', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['188', '189'])).
% 2.35/2.59  thf('191', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['190'])).
% 2.35/2.59  thf('192', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['185', '191'])).
% 2.35/2.59  thf('193', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('195', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['192', '193', '194'])).
% 2.35/2.59  thf('196', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['195'])).
% 2.35/2.59  thf('197', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['184', '196'])).
% 2.35/2.59  thf('198', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('200', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['197', '198', '199'])).
% 2.35/2.59  thf('201', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['200'])).
% 2.35/2.59  thf('202', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['183', '201'])).
% 2.35/2.59  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('205', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['202', '203', '204'])).
% 2.35/2.59  thf('206', plain,
% 2.35/2.59      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['205'])).
% 2.35/2.59  thf('207', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v4_orders_2 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('208', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v7_waybel_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('209', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((l1_waybel_0 @ (sk_B @ X31) @ X31)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('210', plain,
% 2.35/2.59      ((![X35 : $i]:
% 2.35/2.59          ((v2_struct_0 @ X35)
% 2.35/2.59           | ~ (v4_orders_2 @ X35)
% 2.35/2.59           | ~ (v7_waybel_0 @ X35)
% 2.35/2.59           | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59           | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('split', [status(esa)], ['13'])).
% 2.35/2.59  thf('211', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['209', '210'])).
% 2.35/2.59  thf('212', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('214', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('demod', [status(thm)], ['211', '212', '213'])).
% 2.35/2.59  thf('215', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['208', '214'])).
% 2.35/2.59  thf('216', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('218', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('demod', [status(thm)], ['215', '216', '217'])).
% 2.35/2.59  thf('219', plain,
% 2.35/2.59      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['218'])).
% 2.35/2.59  thf('220', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['207', '219'])).
% 2.35/2.59  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('223', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('demod', [status(thm)], ['220', '221', '222'])).
% 2.35/2.59  thf('224', plain,
% 2.35/2.59      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['223'])).
% 2.35/2.59  thf('225', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v7_waybel_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('226', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v4_orders_2 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('227', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((l1_waybel_0 @ (sk_B @ X31) @ X31)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('228', plain,
% 2.35/2.59      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['161'])).
% 2.35/2.59  thf('229', plain,
% 2.35/2.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.59         (~ (l1_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X17)
% 2.35/2.59          | ~ (v4_orders_2 @ X17)
% 2.35/2.59          | ~ (v7_waybel_0 @ X17)
% 2.35/2.59          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.59          | (l1_waybel_0 @ X18 @ X16)
% 2.35/2.59          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.59      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.59  thf('230', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['228', '229'])).
% 2.35/2.59  thf('231', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.59      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.59  thf('232', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['230', '231'])).
% 2.35/2.59  thf('233', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['232'])).
% 2.35/2.59  thf('234', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['227', '233'])).
% 2.35/2.59  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('237', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['234', '235', '236'])).
% 2.35/2.59  thf('238', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['237'])).
% 2.35/2.59  thf('239', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['226', '238'])).
% 2.35/2.59  thf('240', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('242', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['239', '240', '241'])).
% 2.35/2.59  thf('243', plain,
% 2.35/2.59      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['242'])).
% 2.35/2.59  thf('244', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['225', '243'])).
% 2.35/2.59  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('247', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['244', '245', '246'])).
% 2.35/2.59  thf('248', plain,
% 2.35/2.59      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['247'])).
% 2.35/2.59  thf('249', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v7_waybel_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('250', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((v4_orders_2 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('251', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((l1_waybel_0 @ (sk_B @ X31) @ X31)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('252', plain,
% 2.35/2.59      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['161'])).
% 2.35/2.59  thf('253', plain,
% 2.35/2.59      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['205'])).
% 2.35/2.59  thf('254', plain,
% 2.35/2.59      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['181'])).
% 2.35/2.59  thf('255', plain,
% 2.35/2.59      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['247'])).
% 2.35/2.59  thf(d3_tarski, axiom,
% 2.35/2.59    (![A:$i,B:$i]:
% 2.35/2.59     ( ( r1_tarski @ A @ B ) <=>
% 2.35/2.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.35/2.59  thf('256', plain,
% 2.35/2.59      (![X1 : $i, X3 : $i]:
% 2.35/2.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.35/2.59      inference('cnf', [status(esa)], [d3_tarski])).
% 2.35/2.59  thf('257', plain,
% 2.35/2.59      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['181'])).
% 2.35/2.59  thf('258', plain,
% 2.35/2.59      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['205'])).
% 2.35/2.59  thf('259', plain,
% 2.35/2.59      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['247'])).
% 2.35/2.59  thf(dt_k10_yellow_6, axiom,
% 2.35/2.59    (![A:$i,B:$i]:
% 2.35/2.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.35/2.59         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 2.35/2.59         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.59       ( m1_subset_1 @
% 2.35/2.59         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.35/2.59  thf('260', plain,
% 2.35/2.59      (![X14 : $i, X15 : $i]:
% 2.35/2.59         (~ (l1_pre_topc @ X14)
% 2.35/2.59          | ~ (v2_pre_topc @ X14)
% 2.35/2.59          | (v2_struct_0 @ X14)
% 2.35/2.59          | (v2_struct_0 @ X15)
% 2.35/2.59          | ~ (v4_orders_2 @ X15)
% 2.35/2.59          | ~ (v7_waybel_0 @ X15)
% 2.35/2.59          | ~ (l1_waybel_0 @ X15 @ X14)
% 2.35/2.59          | (m1_subset_1 @ (k10_yellow_6 @ X14 @ X15) @ 
% 2.35/2.59             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 2.35/2.59      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 2.35/2.59  thf('261', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 2.35/2.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['259', '260'])).
% 2.35/2.59  thf('262', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('263', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('264', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 2.35/2.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['261', '262', '263'])).
% 2.35/2.59  thf('265', plain,
% 2.35/2.59      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 2.35/2.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['264'])).
% 2.35/2.59  thf('266', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 2.35/2.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['258', '265'])).
% 2.35/2.59  thf('267', plain,
% 2.35/2.59      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 2.35/2.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['266'])).
% 2.35/2.59  thf('268', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 2.35/2.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['257', '267'])).
% 2.35/2.59  thf('269', plain,
% 2.35/2.59      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 2.35/2.59            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['268'])).
% 2.35/2.59  thf(t4_subset, axiom,
% 2.35/2.59    (![A:$i,B:$i,C:$i]:
% 2.35/2.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.35/2.59       ( m1_subset_1 @ A @ C ) ))).
% 2.35/2.59  thf('270', plain,
% 2.35/2.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.35/2.59         (~ (r2_hidden @ X8 @ X9)
% 2.35/2.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.35/2.59          | (m1_subset_1 @ X8 @ X10))),
% 2.35/2.59      inference('cnf', [status(esa)], [t4_subset])).
% 2.35/2.59  thf('271', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 2.35/2.59           | ~ (r2_hidden @ X0 @ 
% 2.35/2.59                (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['269', '270'])).
% 2.35/2.59  thf('272', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (m1_subset_1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))) @ 
% 2.35/2.59              (u1_struct_0 @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['256', '271'])).
% 2.35/2.59  thf('273', plain,
% 2.35/2.59      (![X1 : $i, X3 : $i]:
% 2.35/2.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.35/2.59      inference('cnf', [status(esa)], [d3_tarski])).
% 2.35/2.59  thf(t29_waybel_9, axiom,
% 2.35/2.59    (![A:$i]:
% 2.35/2.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.35/2.59       ( ![B:$i]:
% 2.35/2.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.59             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.59           ( ![C:$i]:
% 2.35/2.59             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.35/2.59               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) =>
% 2.35/2.59                 ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 2.35/2.59  thf('274', plain,
% 2.35/2.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.35/2.59         ((v2_struct_0 @ X21)
% 2.35/2.59          | ~ (v4_orders_2 @ X21)
% 2.35/2.59          | ~ (v7_waybel_0 @ X21)
% 2.35/2.59          | ~ (l1_waybel_0 @ X21 @ X22)
% 2.35/2.59          | ~ (r2_hidden @ X23 @ (k10_yellow_6 @ X22 @ X21))
% 2.35/2.59          | (r3_waybel_9 @ X22 @ X21 @ X23)
% 2.35/2.59          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 2.35/2.59          | ~ (l1_pre_topc @ X22)
% 2.35/2.59          | ~ (v2_pre_topc @ X22)
% 2.35/2.59          | (v2_struct_0 @ X22))),
% 2.35/2.59      inference('cnf', [status(esa)], [t29_waybel_9])).
% 2.35/2.59  thf('275', plain,
% 2.35/2.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.59         ((r1_tarski @ (k10_yellow_6 @ X1 @ X0) @ X2)
% 2.35/2.59          | (v2_struct_0 @ X1)
% 2.35/2.59          | ~ (v2_pre_topc @ X1)
% 2.35/2.59          | ~ (l1_pre_topc @ X1)
% 2.35/2.59          | ~ (m1_subset_1 @ (sk_C @ X2 @ (k10_yellow_6 @ X1 @ X0)) @ 
% 2.35/2.59               (u1_struct_0 @ X1))
% 2.35/2.59          | (r3_waybel_9 @ X1 @ X0 @ (sk_C @ X2 @ (k10_yellow_6 @ X1 @ X0)))
% 2.35/2.59          | ~ (l1_waybel_0 @ X0 @ X1)
% 2.35/2.59          | ~ (v7_waybel_0 @ X0)
% 2.35/2.59          | ~ (v4_orders_2 @ X0)
% 2.35/2.59          | (v2_struct_0 @ X0))),
% 2.35/2.59      inference('sup-', [status(thm)], ['273', '274'])).
% 2.35/2.59  thf('276', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['272', '275'])).
% 2.35/2.59  thf('277', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('278', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('279', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['276', '277', '278'])).
% 2.35/2.59  thf('280', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['279'])).
% 2.35/2.59  thf('281', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['255', '280'])).
% 2.35/2.59  thf('282', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['281'])).
% 2.35/2.59  thf('283', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['254', '282'])).
% 2.35/2.59  thf('284', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['283'])).
% 2.35/2.59  thf('285', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['253', '284'])).
% 2.35/2.59  thf('286', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 2.35/2.59            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['285'])).
% 2.35/2.59  thf('287', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (m1_subset_1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))) @ 
% 2.35/2.59              (u1_struct_0 @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['256', '271'])).
% 2.35/2.59  thf(t31_waybel_9, axiom,
% 2.35/2.59    (![A:$i]:
% 2.35/2.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.35/2.59       ( ![B:$i]:
% 2.35/2.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 2.35/2.59             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 2.35/2.59           ( ![C:$i]:
% 2.35/2.59             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 2.35/2.59               ( ![D:$i]:
% 2.35/2.59                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.35/2.59                   ( ( r3_waybel_9 @ A @ C @ D ) => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 2.35/2.59  thf('288', plain,
% 2.35/2.59      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.35/2.59         ((v2_struct_0 @ X24)
% 2.35/2.59          | ~ (v4_orders_2 @ X24)
% 2.35/2.59          | ~ (v7_waybel_0 @ X24)
% 2.35/2.59          | ~ (l1_waybel_0 @ X24 @ X25)
% 2.35/2.59          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 2.35/2.59          | (r3_waybel_9 @ X25 @ X24 @ X26)
% 2.35/2.59          | ~ (r3_waybel_9 @ X25 @ X27 @ X26)
% 2.35/2.59          | ~ (m2_yellow_6 @ X27 @ X25 @ X24)
% 2.35/2.59          | ~ (l1_pre_topc @ X25)
% 2.35/2.59          | ~ (v2_pre_topc @ X25)
% 2.35/2.59          | (v2_struct_0 @ X25))),
% 2.35/2.59      inference('cnf', [status(esa)], [t31_waybel_9])).
% 2.35/2.59  thf('289', plain,
% 2.35/2.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59           | ~ (m2_yellow_6 @ X2 @ sk_A @ X1)
% 2.35/2.59           | ~ (r3_waybel_9 @ sk_A @ X2 @ 
% 2.35/2.59                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ X1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 2.35/2.59           | ~ (v7_waybel_0 @ X1)
% 2.35/2.59           | ~ (v4_orders_2 @ X1)
% 2.35/2.59           | (v2_struct_0 @ X1)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['287', '288'])).
% 2.35/2.59  thf('290', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('291', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('292', plain,
% 2.35/2.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | ~ (m2_yellow_6 @ X2 @ sk_A @ X1)
% 2.35/2.59           | ~ (r3_waybel_9 @ sk_A @ X2 @ 
% 2.35/2.59                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ X1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 2.35/2.59           | ~ (v7_waybel_0 @ X1)
% 2.35/2.59           | ~ (v4_orders_2 @ X1)
% 2.35/2.59           | (v2_struct_0 @ X1)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['289', '290', '291'])).
% 2.35/2.59  thf('293', plain,
% 2.35/2.59      ((![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.59          ((v2_struct_0 @ X1)
% 2.35/2.59           | ~ (v4_orders_2 @ X1)
% 2.35/2.59           | ~ (v7_waybel_0 @ X1)
% 2.35/2.59           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ X1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (r3_waybel_9 @ sk_A @ X2 @ 
% 2.35/2.59                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (m2_yellow_6 @ X2 @ sk_A @ X1)
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['292'])).
% 2.35/2.59  thf('294', plain,
% 2.35/2.59      ((![X0 : $i, X1 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X1)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ X1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 2.35/2.59           | ~ (v7_waybel_0 @ X1)
% 2.35/2.59           | ~ (v4_orders_2 @ X1)
% 2.35/2.59           | (v2_struct_0 @ X1)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['286', '293'])).
% 2.35/2.59  thf('295', plain,
% 2.35/2.59      ((![X0 : $i, X1 : $i]:
% 2.35/2.59          ((v2_struct_0 @ X1)
% 2.35/2.59           | ~ (v4_orders_2 @ X1)
% 2.35/2.59           | ~ (v7_waybel_0 @ X1)
% 2.35/2.59           | ~ (l1_waybel_0 @ X1 @ sk_A)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ X1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X1)
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['294'])).
% 2.35/2.59  thf('296', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['252', '295'])).
% 2.35/2.59  thf('297', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          (~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59           | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['296'])).
% 2.35/2.59  thf('298', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['251', '297'])).
% 2.35/2.59  thf('299', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('300', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('301', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59           | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['298', '299', '300'])).
% 2.35/2.59  thf('302', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          (~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['301'])).
% 2.35/2.59  thf('303', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['250', '302'])).
% 2.35/2.59  thf('304', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('305', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('306', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['303', '304', '305'])).
% 2.35/2.59  thf('307', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          (~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['306'])).
% 2.35/2.59  thf('308', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['249', '307'])).
% 2.35/2.59  thf('309', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('310', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('311', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['308', '309', '310'])).
% 2.35/2.59  thf('312', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59            (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['311'])).
% 2.35/2.59  thf('313', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (m1_subset_1 @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))) @ 
% 2.35/2.59              (u1_struct_0 @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['256', '271'])).
% 2.35/2.59  thf('314', plain,
% 2.35/2.59      (![X31 : $i, X32 : $i]:
% 2.35/2.59         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 2.35/2.59          | ~ (r3_waybel_9 @ X31 @ (sk_B @ X31) @ X32)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('315', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59           | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['313', '314'])).
% 2.35/2.59  thf('316', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('317', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('318', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59                (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['315', '316', '317'])).
% 2.35/2.59  thf('319', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          (~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 2.35/2.59              (sk_C @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['318'])).
% 2.35/2.59  thf('320', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ sk_A)
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['312', '319'])).
% 2.35/2.59  thf('321', plain,
% 2.35/2.59      ((![X0 : $i]:
% 2.35/2.59          ((r1_tarski @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ X0)
% 2.35/2.59           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59           | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59           | (v1_compts_1 @ sk_A)
% 2.35/2.59           | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['320'])).
% 2.35/2.59  thf('322', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 2.35/2.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.35/2.59  thf(d10_xboole_0, axiom,
% 2.35/2.59    (![A:$i,B:$i]:
% 2.35/2.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.35/2.59  thf('323', plain,
% 2.35/2.59      (![X4 : $i, X6 : $i]:
% 2.35/2.59         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.35/2.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.35/2.59  thf('324', plain,
% 2.35/2.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.35/2.59      inference('sup-', [status(thm)], ['322', '323'])).
% 2.35/2.59  thf('325', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ((k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) = (k1_xboole_0))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['321', '324'])).
% 2.35/2.59  thf('326', plain,
% 2.35/2.59      (![X19 : $i, X20 : $i]:
% 2.35/2.59         ((v2_struct_0 @ X19)
% 2.35/2.59          | ~ (v4_orders_2 @ X19)
% 2.35/2.59          | ~ (v7_waybel_0 @ X19)
% 2.35/2.59          | ~ (l1_waybel_0 @ X19 @ X20)
% 2.35/2.59          | ~ (v3_yellow_6 @ X19 @ X20)
% 2.35/2.59          | ((k10_yellow_6 @ X20 @ X19) != (k1_xboole_0))
% 2.35/2.59          | ~ (l1_pre_topc @ X20)
% 2.35/2.59          | ~ (v2_pre_topc @ X20)
% 2.35/2.59          | (v2_struct_0 @ X20))),
% 2.35/2.59      inference('cnf', [status(esa)], [d19_yellow_6])).
% 2.35/2.59  thf('327', plain,
% 2.35/2.59      (((((k1_xboole_0) != (k1_xboole_0))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['325', '326'])).
% 2.35/2.59  thf('328', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('329', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('330', plain,
% 2.35/2.59      (((((k1_xboole_0) != (k1_xboole_0))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['327', '328', '329'])).
% 2.35/2.59  thf('331', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['330'])).
% 2.35/2.59  thf('332', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['248', '331'])).
% 2.35/2.59  thf('333', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['332'])).
% 2.35/2.59  thf('334', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['224', '333'])).
% 2.35/2.59  thf('335', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['334'])).
% 2.35/2.59  thf('336', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['206', '335'])).
% 2.35/2.59  thf('337', plain,
% 2.35/2.59      (((~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['336'])).
% 2.35/2.59  thf('338', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['182', '337'])).
% 2.35/2.59  thf('339', plain,
% 2.35/2.59      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['338'])).
% 2.35/2.59  thf('340', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         ((l1_waybel_0 @ (sk_B @ X31) @ X31)
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('341', plain,
% 2.35/2.59      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['161'])).
% 2.35/2.59  thf('342', plain,
% 2.35/2.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.35/2.59         (~ (l1_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X16)
% 2.35/2.59          | (v2_struct_0 @ X17)
% 2.35/2.59          | ~ (v4_orders_2 @ X17)
% 2.35/2.59          | ~ (v7_waybel_0 @ X17)
% 2.35/2.59          | ~ (l1_waybel_0 @ X17 @ X16)
% 2.35/2.59          | ~ (v2_struct_0 @ X18)
% 2.35/2.59          | ~ (m2_yellow_6 @ X18 @ X16 @ X17))),
% 2.35/2.59      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 2.35/2.59  thf('343', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (l1_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['341', '342'])).
% 2.35/2.59  thf('344', plain, ((l1_struct_0 @ sk_A)),
% 2.35/2.59      inference('sup-', [status(thm)], ['59', '60'])).
% 2.35/2.59  thf('345', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['343', '344'])).
% 2.35/2.59  thf('346', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['345'])).
% 2.35/2.59  thf('347', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['340', '346'])).
% 2.35/2.59  thf('348', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('349', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('350', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['347', '348', '349'])).
% 2.35/2.59  thf('351', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['350'])).
% 2.35/2.59  thf('352', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['339', '351'])).
% 2.35/2.59  thf('353', plain,
% 2.35/2.59      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['352'])).
% 2.35/2.59  thf('354', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['141', '353'])).
% 2.35/2.59  thf('355', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('356', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('357', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['354', '355', '356'])).
% 2.35/2.59  thf('358', plain,
% 2.35/2.59      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['357'])).
% 2.35/2.59  thf('359', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['140', '358'])).
% 2.35/2.59  thf('360', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('361', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('362', plain,
% 2.35/2.59      ((((v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('demod', [status(thm)], ['359', '360', '361'])).
% 2.35/2.59  thf('363', plain,
% 2.35/2.59      ((((v2_struct_0 @ (sk_B @ sk_A))
% 2.35/2.59         | (v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('simplify', [status(thm)], ['362'])).
% 2.35/2.59  thf('364', plain, (~ (v2_struct_0 @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('365', plain,
% 2.35/2.59      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ (sk_B @ sk_A))))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('clc', [status(thm)], ['363', '364'])).
% 2.35/2.59  thf('366', plain,
% 2.35/2.59      (![X31 : $i]:
% 2.35/2.59         (~ (v2_struct_0 @ (sk_B @ X31))
% 2.35/2.59          | (v1_compts_1 @ X31)
% 2.35/2.59          | ~ (l1_pre_topc @ X31)
% 2.35/2.59          | ~ (v2_pre_topc @ X31)
% 2.35/2.59          | (v2_struct_0 @ X31))),
% 2.35/2.59      inference('cnf', [status(esa)], [t35_yellow19])).
% 2.35/2.59  thf('367', plain,
% 2.35/2.59      ((((v1_compts_1 @ sk_A)
% 2.35/2.59         | (v2_struct_0 @ sk_A)
% 2.35/2.59         | ~ (v2_pre_topc @ sk_A)
% 2.35/2.59         | ~ (l1_pre_topc @ sk_A)
% 2.35/2.59         | (v1_compts_1 @ sk_A)))
% 2.35/2.59         <= ((![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.35/2.59             (![X35 : $i]:
% 2.35/2.59                ((v2_struct_0 @ X35)
% 2.35/2.59                 | ~ (v4_orders_2 @ X35)
% 2.35/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.35/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.35/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.35/2.59      inference('sup-', [status(thm)], ['365', '366'])).
% 2.35/2.59  thf('368', plain, ((v2_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('369', plain, ((l1_pre_topc @ sk_A)),
% 2.35/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.59  thf('370', plain,
% 2.35/2.59      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 2.42/2.59         <= ((![X35 : $i]:
% 2.42/2.59                ((v2_struct_0 @ X35)
% 2.42/2.59                 | ~ (v4_orders_2 @ X35)
% 2.42/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.42/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.42/2.59             (![X35 : $i]:
% 2.42/2.59                ((v2_struct_0 @ X35)
% 2.42/2.59                 | ~ (v4_orders_2 @ X35)
% 2.42/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.42/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.42/2.59      inference('demod', [status(thm)], ['367', '368', '369'])).
% 2.42/2.59  thf('371', plain,
% 2.42/2.59      ((((v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 2.42/2.59         <= ((![X35 : $i]:
% 2.42/2.59                ((v2_struct_0 @ X35)
% 2.42/2.59                 | ~ (v4_orders_2 @ X35)
% 2.42/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.42/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.42/2.59             (![X35 : $i]:
% 2.42/2.59                ((v2_struct_0 @ X35)
% 2.42/2.59                 | ~ (v4_orders_2 @ X35)
% 2.42/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.42/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.42/2.59      inference('simplify', [status(thm)], ['370'])).
% 2.42/2.59  thf('372', plain, (~ (v2_struct_0 @ sk_A)),
% 2.42/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.42/2.59  thf('373', plain,
% 2.42/2.59      (((v1_compts_1 @ sk_A))
% 2.42/2.59         <= ((![X35 : $i]:
% 2.42/2.59                ((v2_struct_0 @ X35)
% 2.42/2.59                 | ~ (v4_orders_2 @ X35)
% 2.42/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.42/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59                 | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) & 
% 2.42/2.59             (![X35 : $i]:
% 2.42/2.59                ((v2_struct_0 @ X35)
% 2.42/2.59                 | ~ (v4_orders_2 @ X35)
% 2.42/2.59                 | ~ (v7_waybel_0 @ X35)
% 2.42/2.59                 | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59                 | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35))))),
% 2.42/2.59      inference('clc', [status(thm)], ['371', '372'])).
% 2.42/2.59  thf('374', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 2.42/2.59      inference('split', [status(esa)], ['2'])).
% 2.42/2.59  thf('375', plain,
% 2.42/2.59      (~
% 2.42/2.59       (![X35 : $i]:
% 2.42/2.59          ((v2_struct_0 @ X35)
% 2.42/2.59           | ~ (v4_orders_2 @ X35)
% 2.42/2.59           | ~ (v7_waybel_0 @ X35)
% 2.42/2.59           | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59           | (v3_yellow_6 @ (sk_C_2 @ X35) @ sk_A))) | 
% 2.42/2.59       ((v1_compts_1 @ sk_A)) | 
% 2.42/2.59       ~
% 2.42/2.59       (![X35 : $i]:
% 2.42/2.59          ((v2_struct_0 @ X35)
% 2.42/2.59           | ~ (v4_orders_2 @ X35)
% 2.42/2.59           | ~ (v7_waybel_0 @ X35)
% 2.42/2.59           | ~ (l1_waybel_0 @ X35 @ sk_A)
% 2.42/2.59           | (m2_yellow_6 @ (sk_C_2 @ X35) @ sk_A @ X35)))),
% 2.42/2.59      inference('sup-', [status(thm)], ['373', '374'])).
% 2.42/2.59  thf('376', plain, ($false),
% 2.42/2.59      inference('sat_resolution*', [status(thm)],
% 2.42/2.59                ['1', '3', '5', '7', '9', '11', '138', '139', '375'])).
% 2.42/2.59  
% 2.42/2.59  % SZS output end Refutation
% 2.42/2.59  
% 2.42/2.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
