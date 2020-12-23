%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0XrtsCMniO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:15:00 EST 2020

% Result     : Theorem 14.43s
% Output     : Refutation 14.48s
% Verified   : 
% Statistics : Number of formulae       :  490 (4125 expanded)
%              Number of leaves         :   41 (1110 expanded)
%              Depth                    :  108
%              Number of atoms          : 11981 (87999 expanded)
%              Number of equality atoms :   84 ( 124 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

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
      | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) )
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
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('13',plain,(
    ! [X37: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v4_orders_2 @ X37 )
      | ~ ( v7_waybel_0 @ X37 )
      | ~ ( l1_waybel_0 @ X37 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A )
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
    ! [X33: $i,X35: $i] :
      ( ~ ( v1_compts_1 @ X33 )
      | ( r3_waybel_9 @ X33 @ X35 @ ( sk_C @ X35 @ X33 ) )
      | ~ ( l1_waybel_0 @ X35 @ X33 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('18',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
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
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
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
    ! [X33: $i,X35: $i] :
      ( ~ ( v1_compts_1 @ X33 )
      | ( m1_subset_1 @ ( sk_C @ X35 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_waybel_0 @ X35 @ X33 )
      | ~ ( v7_waybel_0 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v7_waybel_0 @ X30 )
      | ~ ( l1_waybel_0 @ X30 @ X31 )
      | ( m2_yellow_6 @ ( sk_D_1 @ X32 @ X30 @ X31 ) @ X31 @ X30 )
      | ~ ( r3_waybel_9 @ X31 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( v4_orders_2 @ X20 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
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
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( v7_waybel_0 @ X20 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( l1_waybel_0 @ X20 @ X18 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( ( k10_yellow_6 @ X22 @ X21 )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('99',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v4_orders_2 @ X30 )
      | ~ ( v7_waybel_0 @ X30 )
      | ~ ( l1_waybel_0 @ X30 @ X31 )
      | ( r2_hidden @ X32 @ ( k10_yellow_6 @ X31 @ ( sk_D_1 @ X32 @ X30 @ X31 ) ) )
      | ~ ( r3_waybel_9 @ X31 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('115',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('116',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('121',plain,
    ( ! [X36: $i] :
        ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
   <= ! [X36: $i] :
        ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X36 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
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
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,
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
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m2_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('128',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ~ ( v2_struct_0 @ X20 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('129',plain,
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
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('131',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('132',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('133',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_B_1 )
   <= ( ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['126','137'])).

thf('139',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
   <= ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('140',plain,
    ( ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ! [X36: $i] :
          ( ~ ( m2_yellow_6 @ X36 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X36 @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('142',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('143',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('144',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('145',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('146',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('147',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('148',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('149',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('150',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['147','159'])).

thf('161',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( v7_waybel_0 @ X20 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['146','169'])).

thf('171',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['145','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['144','179'])).

thf('181',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('186',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('187',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('188',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('189',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( v4_orders_2 @ X20 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('190',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['187','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['186','198'])).

thf('200',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['185','203'])).

thf('205',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('210',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('211',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('212',plain,
    ( ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','216'])).

thf('218',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['209','221'])).

thf('223',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('228',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('229',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('230',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('231',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ( l1_waybel_0 @ X20 @ X18 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('232',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('234',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['229','235'])).

thf('237',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['228','240'])).

thf('242',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['227','245'])).

thf('247',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X33: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('252',plain,(
    ! [X33: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('253',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('254',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('255',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('256',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('257',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('258',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('259',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('260',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('261',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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

thf('262',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ( X12
        = ( k10_yellow_6 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('263',plain,(
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
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['260','263'])).

thf('265',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('268',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['259','268'])).

thf('270',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('271',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['258','270'])).

thf('272',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('274',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('275',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('276',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('277',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('278',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('279',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('280',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('281',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('282',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('283',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['249'])).

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

thf('284',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v7_waybel_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('285',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['285','286','287'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['282','289'])).

thf('291',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['281','291'])).

thf('293',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( X12
       != ( k10_yellow_6 @ X11 @ X10 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X14 @ X10 @ X11 ) @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('295',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X11 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X14 @ X10 @ X11 ) @ X11 @ X14 )
      | ( r2_hidden @ X14 @ ( k10_yellow_6 @ X11 @ X10 ) )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['293','295'])).

thf('297',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['280','300'])).

thf('302',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['279','302'])).

thf('304',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['278','304'])).

thf('306',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['277','306'])).

thf('308',plain,
    ( ( ( m1_connsp_2 @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('310',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X12 )
      | ( r1_waybel_0 @ X11 @ X10 @ X13 )
      | ~ ( m1_connsp_2 @ X13 @ X11 @ ( sk_D @ X12 @ X10 @ X11 ) )
      | ( X12
        = ( k10_yellow_6 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('311',plain,(
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
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['308','311'])).

thf('313',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['276','316'])).

thf('318',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['317'])).

thf('319',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['275','318'])).

thf('320',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['274','320'])).

thf('322',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('324',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('325',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('326',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('327',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( X12
       != ( k10_yellow_6 @ X11 @ X10 ) )
      | ( r2_hidden @ X14 @ X12 )
      | ~ ( r1_waybel_0 @ X11 @ X10 @ ( sk_E_1 @ X14 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('328',plain,(
    ! [X10: $i,X11: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X11 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_waybel_0 @ X11 @ X10 @ ( sk_E_1 @ X14 @ X10 @ X11 ) )
      | ( r2_hidden @ X14 @ ( k10_yellow_6 @ X11 @ X10 ) )
      | ~ ( l1_waybel_0 @ X10 @ X11 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['327'])).

thf('329',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['326','328'])).

thf('330',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['329','330','331'])).

thf('333',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['325','333'])).

thf('335',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['324','335'])).

thf('337',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['323','337'])).

thf('339',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['338'])).

thf('340',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['322','339'])).

thf('341',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['340'])).

thf('342',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['273','341'])).

thf('343',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['342'])).

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

thf('344',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( r2_hidden @ X25 @ ( k10_yellow_6 @ X24 @ X23 ) )
      | ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t29_waybel_9])).

thf('345',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['343','344'])).

thf('346',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['345','346','347'])).

thf('349',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['348'])).

thf('350',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['272','349'])).

thf('351',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['350'])).

thf('352',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['257','351'])).

thf('353',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['256','353'])).

thf('355',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['354'])).

thf('356',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['255','355'])).

thf('357',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['271'])).

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

thf('359',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v4_orders_2 @ X26 )
      | ~ ( v7_waybel_0 @ X26 )
      | ~ ( l1_waybel_0 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( r3_waybel_9 @ X27 @ X26 @ X28 )
      | ~ ( r3_waybel_9 @ X27 @ X29 @ X28 )
      | ~ ( m2_yellow_6 @ X29 @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_waybel_9])).

thf('360',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['358','359'])).

thf('361',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('362',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('363',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['360','361','362'])).

thf('364',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['357','364'])).

thf('366',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
        | ( k1_xboole_0
          = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['365'])).

thf('367',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['254','366'])).

thf('368',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['367'])).

thf('369',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['253','368'])).

thf('370',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('372',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['369','370','371'])).

thf('373',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['372'])).

thf('374',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['252','373'])).

thf('375',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['374','375','376'])).

thf('378',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['377'])).

thf('379',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['251','378'])).

thf('380',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('382',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['379','380','381'])).

thf('383',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['382'])).

thf('384',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('385',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( r3_waybel_9 @ X33 @ ( sk_B @ X33 ) @ X34 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('386',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['384','385'])).

thf('387',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('388',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['386','387','388'])).

thf('390',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['383','390'])).

thf('392',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['391'])).

thf('393',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('394',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['392','393'])).

thf('395',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('396',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['394','395'])).

thf('397',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v7_waybel_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( v3_yellow_6 @ X21 @ X22 )
      | ( ( k10_yellow_6 @ X22 @ X21 )
       != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d19_yellow_6])).

thf('398',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['396','397'])).

thf('399',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('401',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['398','399','400'])).

thf('402',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['401'])).

thf('403',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['250','402'])).

thf('404',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['403'])).

thf('405',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['226','404'])).

thf('406',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['208','406'])).

thf('408',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['407'])).

thf('409',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['184','408'])).

thf('410',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['409'])).

thf('411',plain,(
    ! [X33: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X33 ) @ X33 )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('412',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('413',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v7_waybel_0 @ X19 )
      | ~ ( l1_waybel_0 @ X19 @ X18 )
      | ~ ( v2_struct_0 @ X20 )
      | ~ ( m2_yellow_6 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('414',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['412','413'])).

thf('415',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('416',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
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
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['414','415'])).

thf('417',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['416'])).

thf('418',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['411','417'])).

thf('419',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('420',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('421',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(demod,[status(thm)],['418','419','420'])).

thf('422',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X37: $i] :
        ( ( v2_struct_0 @ X37 )
        | ~ ( v4_orders_2 @ X37 )
        | ~ ( v7_waybel_0 @ X37 )
        | ~ ( l1_waybel_0 @ X37 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference(simplify,[status(thm)],['421'])).

thf('423',plain,
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
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['410','422'])).

thf('424',plain,
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
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['423'])).

thf('425',plain,
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
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['143','424'])).

thf('426',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('428',plain,
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
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['425','426','427'])).

thf('429',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['428'])).

thf('430',plain,
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
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['142','429'])).

thf('431',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('432',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('433',plain,
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
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['430','431','432'])).

thf('434',plain,
    ( ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['433'])).

thf('435',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('436',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(clc,[status(thm)],['434','435'])).

thf('437',plain,(
    ! [X33: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X33 ) )
      | ( v1_compts_1 @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('438',plain,
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
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference('sup-',[status(thm)],['436','437'])).

thf('439',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('440',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('441',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('442',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['441'])).

thf('443',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
      & ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ) ),
    inference(clc,[status(thm)],['442','443'])).

thf('445',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('446',plain,
    ( ~ ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ~ ! [X37: $i] :
          ( ( v2_struct_0 @ X37 )
          | ~ ( v4_orders_2 @ X37 )
          | ~ ( v7_waybel_0 @ X37 )
          | ~ ( l1_waybel_0 @ X37 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X37 ) @ sk_A @ X37 ) ) ),
    inference('sup-',[status(thm)],['444','445'])).

thf('447',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','140','141','446'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0XrtsCMniO
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 14.43/14.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.43/14.66  % Solved by: fo/fo7.sh
% 14.43/14.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.43/14.66  % done 12902 iterations in 14.180s
% 14.43/14.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.43/14.66  % SZS output start Refutation
% 14.43/14.66  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 14.43/14.66  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 14.43/14.66  thf(sk_B_type, type, sk_B: $i > $i).
% 14.43/14.66  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 14.43/14.66  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 14.43/14.66  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 14.43/14.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.43/14.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.43/14.66  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 14.43/14.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 14.43/14.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 14.43/14.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 14.43/14.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 14.43/14.66  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 14.43/14.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 14.43/14.66  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 14.43/14.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.43/14.66  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 14.43/14.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.43/14.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 14.43/14.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.43/14.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.43/14.66  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 14.43/14.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 14.43/14.66  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 14.43/14.66  thf(sk_A_type, type, sk_A: $i).
% 14.43/14.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 14.43/14.66  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 14.43/14.66  thf(t37_yellow19, conjecture,
% 14.43/14.66    (![A:$i]:
% 14.43/14.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.43/14.66       ( ( v1_compts_1 @ A ) <=>
% 14.43/14.66         ( ![B:$i]:
% 14.43/14.66           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.43/14.66               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.43/14.66             ( ?[C:$i]:
% 14.43/14.66               ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ))).
% 14.43/14.66  thf(zf_stmt_0, negated_conjecture,
% 14.43/14.66    (~( ![A:$i]:
% 14.43/14.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 14.43/14.66            ( l1_pre_topc @ A ) ) =>
% 14.43/14.66          ( ( v1_compts_1 @ A ) <=>
% 14.43/14.66            ( ![B:$i]:
% 14.43/14.66              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.43/14.66                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.43/14.66                ( ?[C:$i]:
% 14.43/14.66                  ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ) )),
% 14.43/14.66    inference('cnf.neg', [status(esa)], [t37_yellow19])).
% 14.43/14.66  thf('0', plain,
% 14.43/14.66      (![X37 : $i]:
% 14.43/14.66         ((v2_struct_0 @ X37)
% 14.43/14.66          | ~ (v4_orders_2 @ X37)
% 14.43/14.66          | ~ (v7_waybel_0 @ X37)
% 14.43/14.66          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.43/14.66          | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37)
% 14.43/14.66          | (v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('1', plain,
% 14.43/14.66      ((![X37 : $i]:
% 14.43/14.66          ((v2_struct_0 @ X37)
% 14.43/14.66           | ~ (v4_orders_2 @ X37)
% 14.43/14.66           | ~ (v7_waybel_0 @ X37)
% 14.43/14.66           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.43/14.66           | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))) | 
% 14.43/14.66       ((v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('split', [status(esa)], ['0'])).
% 14.43/14.66  thf('2', plain,
% 14.43/14.66      (![X36 : $i]:
% 14.43/14.66         (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 14.43/14.66          | ~ (v3_yellow_6 @ X36 @ sk_A)
% 14.43/14.66          | ~ (v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('3', plain,
% 14.43/14.66      ((![X36 : $i]:
% 14.43/14.66          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 14.43/14.66       ~ ((v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('split', [status(esa)], ['2'])).
% 14.43/14.66  thf('4', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('5', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('split', [status(esa)], ['4'])).
% 14.43/14.66  thf('6', plain, (((v7_waybel_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('7', plain, (((v7_waybel_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('split', [status(esa)], ['6'])).
% 14.43/14.66  thf('8', plain, (((v4_orders_2 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('9', plain, (((v4_orders_2 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('split', [status(esa)], ['8'])).
% 14.43/14.66  thf('10', plain, ((~ (v2_struct_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('11', plain, (~ ((v2_struct_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('split', [status(esa)], ['10'])).
% 14.43/14.66  thf('12', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.43/14.66      inference('split', [status(esa)], ['6'])).
% 14.43/14.66  thf('13', plain,
% 14.43/14.66      (![X37 : $i]:
% 14.43/14.66         ((v2_struct_0 @ X37)
% 14.43/14.66          | ~ (v4_orders_2 @ X37)
% 14.43/14.66          | ~ (v7_waybel_0 @ X37)
% 14.43/14.66          | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.43/14.66          | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A)
% 14.43/14.66          | (v1_compts_1 @ sk_A))),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('14', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 14.43/14.66      inference('split', [status(esa)], ['13'])).
% 14.43/14.66  thf('15', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.43/14.66      inference('split', [status(esa)], ['8'])).
% 14.43/14.66  thf('16', plain,
% 14.43/14.66      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.43/14.66      inference('split', [status(esa)], ['4'])).
% 14.43/14.66  thf(t35_yellow19, axiom,
% 14.43/14.66    (![A:$i]:
% 14.43/14.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.43/14.66       ( ( v1_compts_1 @ A ) <=>
% 14.43/14.66         ( ![B:$i]:
% 14.43/14.66           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.43/14.66               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.43/14.66             ( ?[C:$i]:
% 14.43/14.66               ( ( r3_waybel_9 @ A @ B @ C ) & 
% 14.43/14.66                 ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 14.43/14.66  thf('17', plain,
% 14.43/14.66      (![X33 : $i, X35 : $i]:
% 14.43/14.66         (~ (v1_compts_1 @ X33)
% 14.43/14.66          | (r3_waybel_9 @ X33 @ X35 @ (sk_C @ X35 @ X33))
% 14.43/14.66          | ~ (l1_waybel_0 @ X35 @ X33)
% 14.43/14.66          | ~ (v7_waybel_0 @ X35)
% 14.43/14.66          | ~ (v4_orders_2 @ X35)
% 14.43/14.66          | (v2_struct_0 @ X35)
% 14.43/14.66          | ~ (l1_pre_topc @ X33)
% 14.43/14.66          | ~ (v2_pre_topc @ X33)
% 14.43/14.66          | (v2_struct_0 @ X33))),
% 14.43/14.66      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.43/14.66  thf('18', plain,
% 14.43/14.66      ((((v2_struct_0 @ sk_A)
% 14.43/14.66         | ~ (v2_pre_topc @ sk_A)
% 14.43/14.66         | ~ (l1_pre_topc @ sk_A)
% 14.43/14.66         | (v2_struct_0 @ sk_B_1)
% 14.43/14.66         | ~ (v4_orders_2 @ sk_B_1)
% 14.43/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.43/14.66         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 14.43/14.66         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.43/14.66      inference('sup-', [status(thm)], ['16', '17'])).
% 14.43/14.66  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 14.43/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.43/14.66  thf('21', plain,
% 14.43/14.66      ((((v2_struct_0 @ sk_A)
% 14.43/14.66         | (v2_struct_0 @ sk_B_1)
% 14.43/14.66         | ~ (v4_orders_2 @ sk_B_1)
% 14.43/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.43/14.66         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 14.43/14.66         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.43/14.66      inference('demod', [status(thm)], ['18', '19', '20'])).
% 14.43/14.66  thf('22', plain,
% 14.43/14.66      (((~ (v1_compts_1 @ sk_A)
% 14.43/14.66         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 14.43/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.43/14.66         | (v2_struct_0 @ sk_B_1)
% 14.43/14.66         | (v2_struct_0 @ sk_A)))
% 14.43/14.66         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v4_orders_2 @ sk_B_1)))),
% 14.43/14.66      inference('sup-', [status(thm)], ['15', '21'])).
% 14.43/14.66  thf('23', plain,
% 14.43/14.66      ((((v2_struct_0 @ sk_A)
% 14.43/14.66         | (v2_struct_0 @ sk_B_1)
% 14.43/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.43/14.66         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 14.43/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.43/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.43/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.43/14.66      inference('sup-', [status(thm)], ['14', '22'])).
% 14.43/14.66  thf('24', plain,
% 14.43/14.66      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 14.43/14.66         | (v2_struct_0 @ sk_B_1)
% 14.43/14.66         | (v2_struct_0 @ sk_A)))
% 14.43/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.43/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.43/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.43/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.43/14.66      inference('sup-', [status(thm)], ['12', '23'])).
% 14.48/14.66  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('26', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('clc', [status(thm)], ['24', '25'])).
% 14.48/14.66  thf('27', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['6'])).
% 14.48/14.66  thf('28', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 14.48/14.66      inference('split', [status(esa)], ['13'])).
% 14.48/14.66  thf('29', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['8'])).
% 14.48/14.66  thf('30', plain,
% 14.48/14.66      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.66      inference('split', [status(esa)], ['4'])).
% 14.48/14.66  thf('31', plain,
% 14.48/14.66      (![X33 : $i, X35 : $i]:
% 14.48/14.66         (~ (v1_compts_1 @ X33)
% 14.48/14.66          | (m1_subset_1 @ (sk_C @ X35 @ X33) @ (u1_struct_0 @ X33))
% 14.48/14.66          | ~ (l1_waybel_0 @ X35 @ X33)
% 14.48/14.66          | ~ (v7_waybel_0 @ X35)
% 14.48/14.66          | ~ (v4_orders_2 @ X35)
% 14.48/14.66          | (v2_struct_0 @ X35)
% 14.48/14.66          | ~ (l1_pre_topc @ X33)
% 14.48/14.66          | ~ (v2_pre_topc @ X33)
% 14.48/14.66          | (v2_struct_0 @ X33))),
% 14.48/14.66      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.66  thf('32', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_A)
% 14.48/14.66         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.66         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.66         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 14.48/14.66         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['30', '31'])).
% 14.48/14.66  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('35', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_A)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.66         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 14.48/14.66         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 14.48/14.66  thf('36', plain,
% 14.48/14.66      (((~ (v1_compts_1 @ sk_A)
% 14.48/14.66         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 14.48/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)))
% 14.48/14.66         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['29', '35'])).
% 14.48/14.66  thf('37', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_A)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.66         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['28', '36'])).
% 14.48/14.66  thf('38', plain,
% 14.48/14.66      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['27', '37'])).
% 14.48/14.66  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('40', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('clc', [status(thm)], ['38', '39'])).
% 14.48/14.66  thf(t32_waybel_9, axiom,
% 14.48/14.66    (![A:$i]:
% 14.48/14.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.48/14.66       ( ![B:$i]:
% 14.48/14.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.48/14.66             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.48/14.66           ( ![C:$i]:
% 14.48/14.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.48/14.66               ( ~( ( r3_waybel_9 @ A @ B @ C ) & 
% 14.48/14.66                    ( ![D:$i]:
% 14.48/14.66                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 14.48/14.66                        ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 14.48/14.66  thf('41', plain,
% 14.48/14.66      (![X30 : $i, X31 : $i, X32 : $i]:
% 14.48/14.66         ((v2_struct_0 @ X30)
% 14.48/14.66          | ~ (v4_orders_2 @ X30)
% 14.48/14.66          | ~ (v7_waybel_0 @ X30)
% 14.48/14.66          | ~ (l1_waybel_0 @ X30 @ X31)
% 14.48/14.66          | (m2_yellow_6 @ (sk_D_1 @ X32 @ X30 @ X31) @ X31 @ X30)
% 14.48/14.66          | ~ (r3_waybel_9 @ X31 @ X30 @ X32)
% 14.48/14.66          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 14.48/14.66          | ~ (l1_pre_topc @ X31)
% 14.48/14.66          | ~ (v2_pre_topc @ X31)
% 14.48/14.66          | (v2_struct_0 @ X31))),
% 14.48/14.66      inference('cnf', [status(esa)], [t32_waybel_9])).
% 14.48/14.66  thf('42', plain,
% 14.48/14.66      ((![X0 : $i]:
% 14.48/14.66          ((v2_struct_0 @ sk_B_1)
% 14.48/14.66           | (v2_struct_0 @ sk_A)
% 14.48/14.66           | ~ (v2_pre_topc @ sk_A)
% 14.48/14.66           | ~ (l1_pre_topc @ sk_A)
% 14.48/14.66           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 14.48/14.66           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 14.48/14.66              sk_A @ X0)
% 14.48/14.66           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.66           | ~ (v7_waybel_0 @ X0)
% 14.48/14.66           | ~ (v4_orders_2 @ X0)
% 14.48/14.66           | (v2_struct_0 @ X0)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['40', '41'])).
% 14.48/14.66  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('45', plain,
% 14.48/14.66      ((![X0 : $i]:
% 14.48/14.66          ((v2_struct_0 @ sk_B_1)
% 14.48/14.66           | (v2_struct_0 @ sk_A)
% 14.48/14.66           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 14.48/14.66           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 14.48/14.66              sk_A @ X0)
% 14.48/14.66           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.66           | ~ (v7_waybel_0 @ X0)
% 14.48/14.66           | ~ (v4_orders_2 @ X0)
% 14.48/14.66           | (v2_struct_0 @ X0)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('demod', [status(thm)], ['42', '43', '44'])).
% 14.48/14.66  thf('46', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.66         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 14.48/14.66         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.66            sk_A @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['26', '45'])).
% 14.48/14.66  thf('47', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['8'])).
% 14.48/14.66  thf('48', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['6'])).
% 14.48/14.66  thf('49', plain,
% 14.48/14.66      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.66      inference('split', [status(esa)], ['4'])).
% 14.48/14.66  thf('50', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.66            sk_A @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 14.48/14.66  thf('51', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_A)
% 14.48/14.66         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.66            sk_A @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('simplify', [status(thm)], ['50'])).
% 14.48/14.66  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('53', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.66            sk_A @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('clc', [status(thm)], ['51', '52'])).
% 14.48/14.66  thf(dt_m2_yellow_6, axiom,
% 14.48/14.66    (![A:$i,B:$i]:
% 14.48/14.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 14.48/14.66         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.48/14.66         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.48/14.66       ( ![C:$i]:
% 14.48/14.66         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 14.48/14.66           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 14.48/14.66             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 14.48/14.66  thf('54', plain,
% 14.48/14.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.66         (~ (l1_struct_0 @ X18)
% 14.48/14.66          | (v2_struct_0 @ X18)
% 14.48/14.66          | (v2_struct_0 @ X19)
% 14.48/14.66          | ~ (v4_orders_2 @ X19)
% 14.48/14.66          | ~ (v7_waybel_0 @ X19)
% 14.48/14.66          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.66          | (v4_orders_2 @ X20)
% 14.48/14.66          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.66      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.66  thf('55', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.66         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 14.48/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.66         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)
% 14.48/14.66         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['53', '54'])).
% 14.48/14.66  thf('56', plain,
% 14.48/14.66      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.66      inference('split', [status(esa)], ['4'])).
% 14.48/14.66  thf('57', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['6'])).
% 14.48/14.66  thf('58', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['8'])).
% 14.48/14.66  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf(dt_l1_pre_topc, axiom,
% 14.48/14.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 14.48/14.66  thf('60', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 14.48/14.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 14.48/14.66  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.66      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.66  thf('62', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('demod', [status(thm)], ['55', '56', '57', '58', '61'])).
% 14.48/14.66  thf('63', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_A)
% 14.48/14.66         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('simplify', [status(thm)], ['62'])).
% 14.48/14.66  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('65', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('clc', [status(thm)], ['63', '64'])).
% 14.48/14.66  thf('66', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.66            sk_A @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('clc', [status(thm)], ['51', '52'])).
% 14.48/14.66  thf('67', plain,
% 14.48/14.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.66         (~ (l1_struct_0 @ X18)
% 14.48/14.66          | (v2_struct_0 @ X18)
% 14.48/14.66          | (v2_struct_0 @ X19)
% 14.48/14.66          | ~ (v4_orders_2 @ X19)
% 14.48/14.66          | ~ (v7_waybel_0 @ X19)
% 14.48/14.66          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.66          | (v7_waybel_0 @ X20)
% 14.48/14.66          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.66      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.66  thf('68', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.66         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 14.48/14.66         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.66         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)
% 14.48/14.66         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('sup-', [status(thm)], ['66', '67'])).
% 14.48/14.66  thf('69', plain,
% 14.48/14.66      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.66      inference('split', [status(esa)], ['4'])).
% 14.48/14.66  thf('70', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['6'])).
% 14.48/14.66  thf('71', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('split', [status(esa)], ['8'])).
% 14.48/14.66  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.66      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.66  thf('73', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v2_struct_0 @ sk_A)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 14.48/14.66  thf('74', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_A)
% 14.48/14.66         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.66         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('simplify', [status(thm)], ['73'])).
% 14.48/14.66  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.66  thf('76', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('clc', [status(thm)], ['74', '75'])).
% 14.48/14.66  thf('77', plain,
% 14.48/14.66      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.66         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.66            sk_A @ sk_B_1)))
% 14.48/14.66         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.66             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.66             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.66             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.66      inference('clc', [status(thm)], ['51', '52'])).
% 14.48/14.66  thf('78', plain,
% 14.48/14.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.67         (~ (l1_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X19)
% 14.48/14.67          | ~ (v4_orders_2 @ X19)
% 14.48/14.67          | ~ (v7_waybel_0 @ X19)
% 14.48/14.67          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.67          | (l1_waybel_0 @ X20 @ X18)
% 14.48/14.67          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.67      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.67  thf('79', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.67         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['77', '78'])).
% 14.48/14.67  thf('80', plain,
% 14.48/14.67      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.67      inference('split', [status(esa)], ['4'])).
% 14.48/14.67  thf('81', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.48/14.67      inference('split', [status(esa)], ['6'])).
% 14.48/14.67  thf('82', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('split', [status(esa)], ['8'])).
% 14.48/14.67  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.67      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.67  thf('84', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 14.48/14.67  thf('85', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('simplify', [status(thm)], ['84'])).
% 14.48/14.67  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('87', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['85', '86'])).
% 14.48/14.67  thf(d19_yellow_6, axiom,
% 14.48/14.67    (![A:$i]:
% 14.48/14.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.48/14.67       ( ![B:$i]:
% 14.48/14.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.48/14.67             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.48/14.67           ( ( v3_yellow_6 @ B @ A ) <=>
% 14.48/14.67             ( ( k10_yellow_6 @ A @ B ) != ( k1_xboole_0 ) ) ) ) ) ))).
% 14.48/14.67  thf('88', plain,
% 14.48/14.67      (![X21 : $i, X22 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X21)
% 14.48/14.67          | ~ (v4_orders_2 @ X21)
% 14.48/14.67          | ~ (v7_waybel_0 @ X21)
% 14.48/14.67          | ~ (l1_waybel_0 @ X21 @ X22)
% 14.48/14.67          | ((k10_yellow_6 @ X22 @ X21) = (k1_xboole_0))
% 14.48/14.67          | (v3_yellow_6 @ X21 @ X22)
% 14.48/14.67          | ~ (l1_pre_topc @ X22)
% 14.48/14.67          | ~ (v2_pre_topc @ X22)
% 14.48/14.67          | (v2_struct_0 @ X22))),
% 14.48/14.67      inference('cnf', [status(esa)], [d19_yellow_6])).
% 14.48/14.67  thf('89', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | ((k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['87', '88'])).
% 14.48/14.67  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('92', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | ((k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('demod', [status(thm)], ['89', '90', '91'])).
% 14.48/14.67  thf('93', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | ((k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['76', '92'])).
% 14.48/14.67  thf('94', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | ((k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('simplify', [status(thm)], ['93'])).
% 14.48/14.67  thf('95', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | ((k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['65', '94'])).
% 14.48/14.67  thf('96', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | ((k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('simplify', [status(thm)], ['95'])).
% 14.48/14.67  thf('97', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['24', '25'])).
% 14.48/14.67  thf('98', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['38', '39'])).
% 14.48/14.67  thf('99', plain,
% 14.48/14.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X30)
% 14.48/14.67          | ~ (v4_orders_2 @ X30)
% 14.48/14.67          | ~ (v7_waybel_0 @ X30)
% 14.48/14.67          | ~ (l1_waybel_0 @ X30 @ X31)
% 14.48/14.67          | (r2_hidden @ X32 @ 
% 14.48/14.67             (k10_yellow_6 @ X31 @ (sk_D_1 @ X32 @ X30 @ X31)))
% 14.48/14.67          | ~ (r3_waybel_9 @ X31 @ X30 @ X32)
% 14.48/14.67          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 14.48/14.67          | ~ (l1_pre_topc @ X31)
% 14.48/14.67          | ~ (v2_pre_topc @ X31)
% 14.48/14.67          | (v2_struct_0 @ X31))),
% 14.48/14.67      inference('cnf', [status(esa)], [t32_waybel_9])).
% 14.48/14.67  thf('100', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_B_1)
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67           | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 14.48/14.67           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 14.48/14.67              (k10_yellow_6 @ sk_A @ 
% 14.48/14.67               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 14.48/14.67           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.67           | ~ (v7_waybel_0 @ X0)
% 14.48/14.67           | ~ (v4_orders_2 @ X0)
% 14.48/14.67           | (v2_struct_0 @ X0)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['98', '99'])).
% 14.48/14.67  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('103', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_B_1)
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 14.48/14.67           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 14.48/14.67              (k10_yellow_6 @ sk_A @ 
% 14.48/14.67               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 14.48/14.67           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.67           | ~ (v7_waybel_0 @ X0)
% 14.48/14.67           | ~ (v4_orders_2 @ X0)
% 14.48/14.67           | (v2_struct_0 @ X0)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('demod', [status(thm)], ['100', '101', '102'])).
% 14.48/14.67  thf('104', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.67         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.67         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 14.48/14.67         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['97', '103'])).
% 14.48/14.67  thf('105', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('split', [status(esa)], ['8'])).
% 14.48/14.67  thf('106', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.48/14.67      inference('split', [status(esa)], ['6'])).
% 14.48/14.67  thf('107', plain,
% 14.48/14.67      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.67      inference('split', [status(esa)], ['4'])).
% 14.48/14.67  thf('108', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 14.48/14.67  thf('109', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('simplify', [status(thm)], ['108'])).
% 14.48/14.67  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('111', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ 
% 14.48/14.67             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['109', '110'])).
% 14.48/14.67  thf(t7_ordinal1, axiom,
% 14.48/14.67    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.48/14.67  thf('112', plain,
% 14.48/14.67      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 14.48/14.67      inference('cnf', [status(esa)], [t7_ordinal1])).
% 14.48/14.67  thf('113', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | ~ (r1_tarski @ 
% 14.48/14.67              (k10_yellow_6 @ sk_A @ 
% 14.48/14.67               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) @ 
% 14.48/14.67              (sk_C @ sk_B_1 @ sk_A))))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['111', '112'])).
% 14.48/14.67  thf('114', plain,
% 14.48/14.67      (((~ (r1_tarski @ k1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['96', '113'])).
% 14.48/14.67  thf(t4_subset_1, axiom,
% 14.48/14.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 14.48/14.67  thf('115', plain,
% 14.48/14.67      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 14.48/14.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.48/14.67  thf(t3_subset, axiom,
% 14.48/14.67    (![A:$i,B:$i]:
% 14.48/14.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.48/14.67  thf('116', plain,
% 14.48/14.67      (![X1 : $i, X2 : $i]:
% 14.48/14.67         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 14.48/14.67      inference('cnf', [status(esa)], [t3_subset])).
% 14.48/14.67  thf('117', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 14.48/14.67      inference('sup-', [status(thm)], ['115', '116'])).
% 14.48/14.67  thf('118', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('demod', [status(thm)], ['114', '117'])).
% 14.48/14.67  thf('119', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('simplify', [status(thm)], ['118'])).
% 14.48/14.67  thf('120', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['51', '52'])).
% 14.48/14.67  thf('121', plain,
% 14.48/14.67      ((![X36 : $i]:
% 14.48/14.67          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A)))
% 14.48/14.67         <= ((![X36 : $i]:
% 14.48/14.67                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 14.48/14.67                 | ~ (v3_yellow_6 @ X36 @ sk_A))))),
% 14.48/14.67      inference('split', [status(esa)], ['2'])).
% 14.48/14.67  thf('122', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | ~ (v3_yellow_6 @ 
% 14.48/14.67              (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ sk_A)))
% 14.48/14.67         <= ((![X36 : $i]:
% 14.48/14.67                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 14.48/14.67                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 14.48/14.67             ((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['120', '121'])).
% 14.48/14.67  thf('123', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= ((![X36 : $i]:
% 14.48/14.67                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 14.48/14.67                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 14.48/14.67             ((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['119', '122'])).
% 14.48/14.67  thf('124', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= ((![X36 : $i]:
% 14.48/14.67                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 14.48/14.67                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 14.48/14.67             ((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('simplify', [status(thm)], ['123'])).
% 14.48/14.67  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('126', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 14.48/14.67         <= ((![X36 : $i]:
% 14.48/14.67                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 14.48/14.67                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 14.48/14.67             ((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['124', '125'])).
% 14.48/14.67  thf('127', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 14.48/14.67            sk_A @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['51', '52'])).
% 14.48/14.67  thf('128', plain,
% 14.48/14.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.67         (~ (l1_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X19)
% 14.48/14.67          | ~ (v4_orders_2 @ X19)
% 14.48/14.67          | ~ (v7_waybel_0 @ X19)
% 14.48/14.67          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.67          | ~ (v2_struct_0 @ X20)
% 14.48/14.67          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.67      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.67  thf('129', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ sk_B_1)
% 14.48/14.67         | ~ (v4_orders_2 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('sup-', [status(thm)], ['127', '128'])).
% 14.48/14.67  thf('130', plain,
% 14.48/14.67      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 14.48/14.67      inference('split', [status(esa)], ['4'])).
% 14.48/14.67  thf('131', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 14.48/14.67      inference('split', [status(esa)], ['6'])).
% 14.48/14.67  thf('132', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('split', [status(esa)], ['8'])).
% 14.48/14.67  thf('133', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.67      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.67  thf('134', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 14.48/14.67  thf('135', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_B_1)))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('simplify', [status(thm)], ['134'])).
% 14.48/14.67  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('137', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_B_1)
% 14.48/14.67         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 14.48/14.67         <= (((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['135', '136'])).
% 14.48/14.67  thf('138', plain,
% 14.48/14.67      (((v2_struct_0 @ sk_B_1))
% 14.48/14.67         <= ((![X36 : $i]:
% 14.48/14.67                (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1)
% 14.48/14.67                 | ~ (v3_yellow_6 @ X36 @ sk_A))) & 
% 14.48/14.67             ((v1_compts_1 @ sk_A)) & 
% 14.48/14.67             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 14.48/14.67             ((v7_waybel_0 @ sk_B_1)) & 
% 14.48/14.67             ((v4_orders_2 @ sk_B_1)))),
% 14.48/14.67      inference('clc', [status(thm)], ['126', '137'])).
% 14.48/14.67  thf('139', plain,
% 14.48/14.67      ((~ (v2_struct_0 @ sk_B_1)) <= (~ ((v2_struct_0 @ sk_B_1)))),
% 14.48/14.67      inference('split', [status(esa)], ['10'])).
% 14.48/14.67  thf('140', plain,
% 14.48/14.67      (~ ((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A)) | 
% 14.48/14.67       ~
% 14.48/14.67       (![X36 : $i]:
% 14.48/14.67          (~ (m2_yellow_6 @ X36 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X36 @ sk_A))) | 
% 14.48/14.67       ~ ((v7_waybel_0 @ sk_B_1)) | ~ ((v4_orders_2 @ sk_B_1)) | 
% 14.48/14.67       ((v2_struct_0 @ sk_B_1))),
% 14.48/14.67      inference('sup-', [status(thm)], ['138', '139'])).
% 14.48/14.67  thf('141', plain,
% 14.48/14.67      ((![X37 : $i]:
% 14.48/14.67          ((v2_struct_0 @ X37)
% 14.48/14.67           | ~ (v4_orders_2 @ X37)
% 14.48/14.67           | ~ (v7_waybel_0 @ X37)
% 14.48/14.67           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67           | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) | 
% 14.48/14.67       ((v1_compts_1 @ sk_A))),
% 14.48/14.67      inference('split', [status(esa)], ['13'])).
% 14.48/14.67  thf('142', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v7_waybel_0 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('143', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v4_orders_2 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('144', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v7_waybel_0 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('145', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v4_orders_2 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('146', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('147', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v4_orders_2 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('148', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v7_waybel_0 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('149', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('150', plain,
% 14.48/14.67      ((![X37 : $i]:
% 14.48/14.67          ((v2_struct_0 @ X37)
% 14.48/14.67           | ~ (v4_orders_2 @ X37)
% 14.48/14.67           | ~ (v7_waybel_0 @ X37)
% 14.48/14.67           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67           | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('split', [status(esa)], ['0'])).
% 14.48/14.67  thf('151', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['149', '150'])).
% 14.48/14.67  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('154', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['151', '152', '153'])).
% 14.48/14.67  thf('155', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['148', '154'])).
% 14.48/14.67  thf('156', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('158', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['155', '156', '157'])).
% 14.48/14.67  thf('159', plain,
% 14.48/14.67      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['158'])).
% 14.48/14.67  thf('160', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['147', '159'])).
% 14.48/14.67  thf('161', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('162', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('163', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['160', '161', '162'])).
% 14.48/14.67  thf('164', plain,
% 14.48/14.67      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['163'])).
% 14.48/14.67  thf('165', plain,
% 14.48/14.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.67         (~ (l1_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X19)
% 14.48/14.67          | ~ (v4_orders_2 @ X19)
% 14.48/14.67          | ~ (v7_waybel_0 @ X19)
% 14.48/14.67          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.67          | (v7_waybel_0 @ X20)
% 14.48/14.67          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.67      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.67  thf('166', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['164', '165'])).
% 14.48/14.67  thf('167', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.67      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.67  thf('168', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['166', '167'])).
% 14.48/14.67  thf('169', plain,
% 14.48/14.67      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['168'])).
% 14.48/14.67  thf('170', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['146', '169'])).
% 14.48/14.67  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('173', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['170', '171', '172'])).
% 14.48/14.67  thf('174', plain,
% 14.48/14.67      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['173'])).
% 14.48/14.67  thf('175', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['145', '174'])).
% 14.48/14.67  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('178', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['175', '176', '177'])).
% 14.48/14.67  thf('179', plain,
% 14.48/14.67      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['178'])).
% 14.48/14.67  thf('180', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['144', '179'])).
% 14.48/14.67  thf('181', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('182', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('183', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['180', '181', '182'])).
% 14.48/14.67  thf('184', plain,
% 14.48/14.67      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['183'])).
% 14.48/14.67  thf('185', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v4_orders_2 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('186', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v7_waybel_0 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('187', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('188', plain,
% 14.48/14.67      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['163'])).
% 14.48/14.67  thf('189', plain,
% 14.48/14.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.67         (~ (l1_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X19)
% 14.48/14.67          | ~ (v4_orders_2 @ X19)
% 14.48/14.67          | ~ (v7_waybel_0 @ X19)
% 14.48/14.67          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.67          | (v4_orders_2 @ X20)
% 14.48/14.67          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.67      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.67  thf('190', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['188', '189'])).
% 14.48/14.67  thf('191', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.67      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.67  thf('192', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['190', '191'])).
% 14.48/14.67  thf('193', plain,
% 14.48/14.67      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['192'])).
% 14.48/14.67  thf('194', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['187', '193'])).
% 14.48/14.67  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('197', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['194', '195', '196'])).
% 14.48/14.67  thf('198', plain,
% 14.48/14.67      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['197'])).
% 14.48/14.67  thf('199', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['186', '198'])).
% 14.48/14.67  thf('200', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('202', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['199', '200', '201'])).
% 14.48/14.67  thf('203', plain,
% 14.48/14.67      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['202'])).
% 14.48/14.67  thf('204', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['185', '203'])).
% 14.48/14.67  thf('205', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('207', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['204', '205', '206'])).
% 14.48/14.67  thf('208', plain,
% 14.48/14.67      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['207'])).
% 14.48/14.67  thf('209', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v4_orders_2 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('210', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v7_waybel_0 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('211', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('212', plain,
% 14.48/14.67      ((![X37 : $i]:
% 14.48/14.67          ((v2_struct_0 @ X37)
% 14.48/14.67           | ~ (v4_orders_2 @ X37)
% 14.48/14.67           | ~ (v7_waybel_0 @ X37)
% 14.48/14.67           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67           | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('split', [status(esa)], ['13'])).
% 14.48/14.67  thf('213', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['211', '212'])).
% 14.48/14.67  thf('214', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('215', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('216', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('demod', [status(thm)], ['213', '214', '215'])).
% 14.48/14.67  thf('217', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['210', '216'])).
% 14.48/14.67  thf('218', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('220', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('demod', [status(thm)], ['217', '218', '219'])).
% 14.48/14.67  thf('221', plain,
% 14.48/14.67      ((((v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['220'])).
% 14.48/14.67  thf('222', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['209', '221'])).
% 14.48/14.67  thf('223', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('225', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('demod', [status(thm)], ['222', '223', '224'])).
% 14.48/14.67  thf('226', plain,
% 14.48/14.67      ((((v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['225'])).
% 14.48/14.67  thf('227', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v7_waybel_0 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('228', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v4_orders_2 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('229', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('230', plain,
% 14.48/14.67      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['163'])).
% 14.48/14.67  thf('231', plain,
% 14.48/14.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.67         (~ (l1_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X18)
% 14.48/14.67          | (v2_struct_0 @ X19)
% 14.48/14.67          | ~ (v4_orders_2 @ X19)
% 14.48/14.67          | ~ (v7_waybel_0 @ X19)
% 14.48/14.67          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.67          | (l1_waybel_0 @ X20 @ X18)
% 14.48/14.67          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.67      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.67  thf('232', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['230', '231'])).
% 14.48/14.67  thf('233', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.67      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.67  thf('234', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['232', '233'])).
% 14.48/14.67  thf('235', plain,
% 14.48/14.67      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['234'])).
% 14.48/14.67  thf('236', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['229', '235'])).
% 14.48/14.67  thf('237', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('238', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('239', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['236', '237', '238'])).
% 14.48/14.67  thf('240', plain,
% 14.48/14.67      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['239'])).
% 14.48/14.67  thf('241', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['228', '240'])).
% 14.48/14.67  thf('242', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('244', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['241', '242', '243'])).
% 14.48/14.67  thf('245', plain,
% 14.48/14.67      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['244'])).
% 14.48/14.67  thf('246', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['227', '245'])).
% 14.48/14.67  thf('247', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('248', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('249', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['246', '247', '248'])).
% 14.48/14.67  thf('250', plain,
% 14.48/14.67      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['249'])).
% 14.48/14.67  thf('251', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v7_waybel_0 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('252', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((v4_orders_2 @ (sk_B @ X33))
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('253', plain,
% 14.48/14.67      (![X33 : $i]:
% 14.48/14.67         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 14.48/14.67          | (v1_compts_1 @ X33)
% 14.48/14.67          | ~ (l1_pre_topc @ X33)
% 14.48/14.67          | ~ (v2_pre_topc @ X33)
% 14.48/14.67          | (v2_struct_0 @ X33))),
% 14.48/14.67      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.67  thf('254', plain,
% 14.48/14.67      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['163'])).
% 14.48/14.67  thf('255', plain,
% 14.48/14.67      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['183'])).
% 14.48/14.67  thf('256', plain,
% 14.48/14.67      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['207'])).
% 14.48/14.67  thf('257', plain,
% 14.48/14.67      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['249'])).
% 14.48/14.67  thf('258', plain,
% 14.48/14.67      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['207'])).
% 14.48/14.67  thf('259', plain,
% 14.48/14.67      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['183'])).
% 14.48/14.67  thf('260', plain,
% 14.48/14.67      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['249'])).
% 14.48/14.67  thf('261', plain,
% 14.48/14.67      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 14.48/14.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.48/14.67  thf(d18_yellow_6, axiom,
% 14.48/14.67    (![A:$i]:
% 14.48/14.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.48/14.67       ( ![B:$i]:
% 14.48/14.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.48/14.67             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.48/14.67           ( ![C:$i]:
% 14.48/14.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.48/14.67               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 14.48/14.67                 ( ![D:$i]:
% 14.48/14.67                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 14.48/14.67                     ( ( r2_hidden @ D @ C ) <=>
% 14.48/14.67                       ( ![E:$i]:
% 14.48/14.67                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 14.48/14.67                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 14.48/14.67  thf('262', plain,
% 14.48/14.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X10)
% 14.48/14.67          | ~ (v4_orders_2 @ X10)
% 14.48/14.67          | ~ (v7_waybel_0 @ X10)
% 14.48/14.67          | ~ (l1_waybel_0 @ X10 @ X11)
% 14.48/14.67          | (m1_subset_1 @ (sk_D @ X12 @ X10 @ X11) @ (u1_struct_0 @ X11))
% 14.48/14.67          | ((X12) = (k10_yellow_6 @ X11 @ X10))
% 14.48/14.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.48/14.67          | ~ (l1_pre_topc @ X11)
% 14.48/14.67          | ~ (v2_pre_topc @ X11)
% 14.48/14.67          | (v2_struct_0 @ X11))),
% 14.48/14.67      inference('cnf', [status(esa)], [d18_yellow_6])).
% 14.48/14.67  thf('263', plain,
% 14.48/14.67      (![X0 : $i, X1 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X0)
% 14.48/14.67          | ~ (v2_pre_topc @ X0)
% 14.48/14.67          | ~ (l1_pre_topc @ X0)
% 14.48/14.67          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 14.48/14.67          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ (u1_struct_0 @ X0))
% 14.48/14.67          | ~ (l1_waybel_0 @ X1 @ X0)
% 14.48/14.67          | ~ (v7_waybel_0 @ X1)
% 14.48/14.67          | ~ (v4_orders_2 @ X1)
% 14.48/14.67          | (v2_struct_0 @ X1))),
% 14.48/14.67      inference('sup-', [status(thm)], ['261', '262'])).
% 14.48/14.67  thf('264', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['260', '263'])).
% 14.48/14.67  thf('265', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('266', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('267', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['264', '265', '266'])).
% 14.48/14.67  thf('268', plain,
% 14.48/14.67      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['267'])).
% 14.48/14.67  thf('269', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['259', '268'])).
% 14.48/14.67  thf('270', plain,
% 14.48/14.67      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['269'])).
% 14.48/14.67  thf('271', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['258', '270'])).
% 14.48/14.67  thf('272', plain,
% 14.48/14.67      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['271'])).
% 14.48/14.67  thf('273', plain,
% 14.48/14.67      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['271'])).
% 14.48/14.67  thf('274', plain,
% 14.48/14.67      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['207'])).
% 14.48/14.67  thf('275', plain,
% 14.48/14.67      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['183'])).
% 14.48/14.67  thf('276', plain,
% 14.48/14.67      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['249'])).
% 14.48/14.67  thf('277', plain,
% 14.48/14.67      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['271'])).
% 14.48/14.67  thf('278', plain,
% 14.48/14.67      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['207'])).
% 14.48/14.67  thf('279', plain,
% 14.48/14.67      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['183'])).
% 14.48/14.67  thf('280', plain,
% 14.48/14.67      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['249'])).
% 14.48/14.67  thf('281', plain,
% 14.48/14.67      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['183'])).
% 14.48/14.67  thf('282', plain,
% 14.48/14.67      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['207'])).
% 14.48/14.67  thf('283', plain,
% 14.48/14.67      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['249'])).
% 14.48/14.67  thf(dt_k10_yellow_6, axiom,
% 14.48/14.67    (![A:$i,B:$i]:
% 14.48/14.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 14.48/14.67         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 14.48/14.67         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.48/14.67       ( m1_subset_1 @
% 14.48/14.67         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 14.48/14.67  thf('284', plain,
% 14.48/14.67      (![X16 : $i, X17 : $i]:
% 14.48/14.67         (~ (l1_pre_topc @ X16)
% 14.48/14.67          | ~ (v2_pre_topc @ X16)
% 14.48/14.67          | (v2_struct_0 @ X16)
% 14.48/14.67          | (v2_struct_0 @ X17)
% 14.48/14.67          | ~ (v4_orders_2 @ X17)
% 14.48/14.67          | ~ (v7_waybel_0 @ X17)
% 14.48/14.67          | ~ (l1_waybel_0 @ X17 @ X16)
% 14.48/14.67          | (m1_subset_1 @ (k10_yellow_6 @ X16 @ X17) @ 
% 14.48/14.67             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 14.48/14.67      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 14.48/14.67  thf('285', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['283', '284'])).
% 14.48/14.67  thf('286', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('287', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('288', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['285', '286', '287'])).
% 14.48/14.67  thf('289', plain,
% 14.48/14.67      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['288'])).
% 14.48/14.67  thf('290', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['282', '289'])).
% 14.48/14.67  thf('291', plain,
% 14.48/14.67      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['290'])).
% 14.48/14.67  thf('292', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['281', '291'])).
% 14.48/14.67  thf('293', plain,
% 14.48/14.67      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['292'])).
% 14.48/14.67  thf('294', plain,
% 14.48/14.67      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X10)
% 14.48/14.67          | ~ (v4_orders_2 @ X10)
% 14.48/14.67          | ~ (v7_waybel_0 @ X10)
% 14.48/14.67          | ~ (l1_waybel_0 @ X10 @ X11)
% 14.48/14.67          | ((X12) != (k10_yellow_6 @ X11 @ X10))
% 14.48/14.67          | (r2_hidden @ X14 @ X12)
% 14.48/14.67          | (m1_connsp_2 @ (sk_E_1 @ X14 @ X10 @ X11) @ X11 @ X14)
% 14.48/14.67          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 14.48/14.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.48/14.67          | ~ (l1_pre_topc @ X11)
% 14.48/14.67          | ~ (v2_pre_topc @ X11)
% 14.48/14.67          | (v2_struct_0 @ X11))),
% 14.48/14.67      inference('cnf', [status(esa)], [d18_yellow_6])).
% 14.48/14.67  thf('295', plain,
% 14.48/14.67      (![X10 : $i, X11 : $i, X14 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X11)
% 14.48/14.67          | ~ (v2_pre_topc @ X11)
% 14.48/14.67          | ~ (l1_pre_topc @ X11)
% 14.48/14.67          | ~ (m1_subset_1 @ (k10_yellow_6 @ X11 @ X10) @ 
% 14.48/14.67               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.48/14.67          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 14.48/14.67          | (m1_connsp_2 @ (sk_E_1 @ X14 @ X10 @ X11) @ X11 @ X14)
% 14.48/14.67          | (r2_hidden @ X14 @ (k10_yellow_6 @ X11 @ X10))
% 14.48/14.67          | ~ (l1_waybel_0 @ X10 @ X11)
% 14.48/14.67          | ~ (v7_waybel_0 @ X10)
% 14.48/14.67          | ~ (v4_orders_2 @ X10)
% 14.48/14.67          | (v2_struct_0 @ X10))),
% 14.48/14.67      inference('simplify', [status(thm)], ['294'])).
% 14.48/14.67  thf('296', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67           | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['293', '295'])).
% 14.48/14.67  thf('297', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('298', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('299', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['296', '297', '298'])).
% 14.48/14.67  thf('300', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['299'])).
% 14.48/14.67  thf('301', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['280', '300'])).
% 14.48/14.67  thf('302', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['301'])).
% 14.48/14.67  thf('303', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['279', '302'])).
% 14.48/14.67  thf('304', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['303'])).
% 14.48/14.67  thf('305', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['278', '304'])).
% 14.48/14.67  thf('306', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              sk_A @ X0)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['305'])).
% 14.48/14.67  thf('307', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (m1_connsp_2 @ 
% 14.48/14.67            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['277', '306'])).
% 14.48/14.67  thf('308', plain,
% 14.48/14.67      ((((m1_connsp_2 @ 
% 14.48/14.67          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67          sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['307'])).
% 14.48/14.67  thf('309', plain,
% 14.48/14.67      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 14.48/14.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.48/14.67  thf('310', plain,
% 14.48/14.67      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X10)
% 14.48/14.67          | ~ (v4_orders_2 @ X10)
% 14.48/14.67          | ~ (v7_waybel_0 @ X10)
% 14.48/14.67          | ~ (l1_waybel_0 @ X10 @ X11)
% 14.48/14.67          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X12)
% 14.48/14.67          | (r1_waybel_0 @ X11 @ X10 @ X13)
% 14.48/14.67          | ~ (m1_connsp_2 @ X13 @ X11 @ (sk_D @ X12 @ X10 @ X11))
% 14.48/14.67          | ((X12) = (k10_yellow_6 @ X11 @ X10))
% 14.48/14.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.48/14.67          | ~ (l1_pre_topc @ X11)
% 14.48/14.67          | ~ (v2_pre_topc @ X11)
% 14.48/14.67          | (v2_struct_0 @ X11))),
% 14.48/14.67      inference('cnf', [status(esa)], [d18_yellow_6])).
% 14.48/14.67  thf('311', plain,
% 14.48/14.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X0)
% 14.48/14.67          | ~ (v2_pre_topc @ X0)
% 14.48/14.67          | ~ (l1_pre_topc @ X0)
% 14.48/14.67          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 14.48/14.67          | ~ (m1_connsp_2 @ X2 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0))
% 14.48/14.67          | (r1_waybel_0 @ X0 @ X1 @ X2)
% 14.48/14.67          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 14.48/14.67          | ~ (l1_waybel_0 @ X1 @ X0)
% 14.48/14.67          | ~ (v7_waybel_0 @ X1)
% 14.48/14.67          | ~ (v4_orders_2 @ X1)
% 14.48/14.67          | (v2_struct_0 @ X1))),
% 14.48/14.67      inference('sup-', [status(thm)], ['309', '310'])).
% 14.48/14.67  thf('312', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['308', '311'])).
% 14.48/14.67  thf('313', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('314', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('315', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['312', '313', '314'])).
% 14.48/14.67  thf('316', plain,
% 14.48/14.67      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['315'])).
% 14.48/14.67  thf('317', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['276', '316'])).
% 14.48/14.67  thf('318', plain,
% 14.48/14.67      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['317'])).
% 14.48/14.67  thf('319', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['275', '318'])).
% 14.48/14.67  thf('320', plain,
% 14.48/14.67      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['319'])).
% 14.48/14.67  thf('321', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['274', '320'])).
% 14.48/14.67  thf('322', plain,
% 14.48/14.67      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['321'])).
% 14.48/14.67  thf('323', plain,
% 14.48/14.67      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['207'])).
% 14.48/14.67  thf('324', plain,
% 14.48/14.67      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['183'])).
% 14.48/14.67  thf('325', plain,
% 14.48/14.67      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['249'])).
% 14.48/14.67  thf('326', plain,
% 14.48/14.67      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 14.48/14.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['292'])).
% 14.48/14.67  thf('327', plain,
% 14.48/14.67      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X10)
% 14.48/14.67          | ~ (v4_orders_2 @ X10)
% 14.48/14.67          | ~ (v7_waybel_0 @ X10)
% 14.48/14.67          | ~ (l1_waybel_0 @ X10 @ X11)
% 14.48/14.67          | ((X12) != (k10_yellow_6 @ X11 @ X10))
% 14.48/14.67          | (r2_hidden @ X14 @ X12)
% 14.48/14.67          | ~ (r1_waybel_0 @ X11 @ X10 @ (sk_E_1 @ X14 @ X10 @ X11))
% 14.48/14.67          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 14.48/14.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.48/14.67          | ~ (l1_pre_topc @ X11)
% 14.48/14.67          | ~ (v2_pre_topc @ X11)
% 14.48/14.67          | (v2_struct_0 @ X11))),
% 14.48/14.67      inference('cnf', [status(esa)], [d18_yellow_6])).
% 14.48/14.67  thf('328', plain,
% 14.48/14.67      (![X10 : $i, X11 : $i, X14 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X11)
% 14.48/14.67          | ~ (v2_pre_topc @ X11)
% 14.48/14.67          | ~ (l1_pre_topc @ X11)
% 14.48/14.67          | ~ (m1_subset_1 @ (k10_yellow_6 @ X11 @ X10) @ 
% 14.48/14.67               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 14.48/14.67          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 14.48/14.67          | ~ (r1_waybel_0 @ X11 @ X10 @ (sk_E_1 @ X14 @ X10 @ X11))
% 14.48/14.67          | (r2_hidden @ X14 @ (k10_yellow_6 @ X11 @ X10))
% 14.48/14.67          | ~ (l1_waybel_0 @ X10 @ X11)
% 14.48/14.67          | ~ (v7_waybel_0 @ X10)
% 14.48/14.67          | ~ (v4_orders_2 @ X10)
% 14.48/14.67          | (v2_struct_0 @ X10))),
% 14.48/14.67      inference('simplify', [status(thm)], ['327'])).
% 14.48/14.67  thf('329', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | ~ (l1_pre_topc @ sk_A)
% 14.48/14.67           | ~ (v2_pre_topc @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['326', '328'])).
% 14.48/14.67  thf('330', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('331', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.67  thf('332', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('demod', [status(thm)], ['329', '330', '331'])).
% 14.48/14.67  thf('333', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['332'])).
% 14.48/14.67  thf('334', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['325', '333'])).
% 14.48/14.67  thf('335', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['334'])).
% 14.48/14.67  thf('336', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['324', '335'])).
% 14.48/14.67  thf('337', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['336'])).
% 14.48/14.67  thf('338', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          ((v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ sk_A)
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['323', '337'])).
% 14.48/14.67  thf('339', plain,
% 14.48/14.67      ((![X0 : $i]:
% 14.48/14.67          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 14.48/14.67           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.67                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.67           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67           | (v1_compts_1 @ sk_A)
% 14.48/14.67           | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['338'])).
% 14.48/14.67  thf('340', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ~ (m1_subset_1 @ 
% 14.48/14.67              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67              (u1_struct_0 @ sk_A))))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['322', '339'])).
% 14.48/14.67  thf('341', plain,
% 14.48/14.67      (((~ (m1_subset_1 @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (u1_struct_0 @ sk_A))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['340'])).
% 14.48/14.67  thf('342', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            k1_xboole_0)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('sup-', [status(thm)], ['273', '341'])).
% 14.48/14.67  thf('343', plain,
% 14.48/14.67      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67          k1_xboole_0)
% 14.48/14.67         | (r2_hidden @ 
% 14.48/14.67            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.67            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.67         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.67         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.67         | (v2_struct_0 @ sk_A)))
% 14.48/14.67         <= ((![X37 : $i]:
% 14.48/14.67                ((v2_struct_0 @ X37)
% 14.48/14.67                 | ~ (v4_orders_2 @ X37)
% 14.48/14.67                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.67                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.67                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.67      inference('simplify', [status(thm)], ['342'])).
% 14.48/14.67  thf(t29_waybel_9, axiom,
% 14.48/14.67    (![A:$i]:
% 14.48/14.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.48/14.67       ( ![B:$i]:
% 14.48/14.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.48/14.67             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.48/14.67           ( ![C:$i]:
% 14.48/14.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.48/14.67               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) =>
% 14.48/14.67                 ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 14.48/14.67  thf('344', plain,
% 14.48/14.67      (![X23 : $i, X24 : $i, X25 : $i]:
% 14.48/14.67         ((v2_struct_0 @ X23)
% 14.48/14.67          | ~ (v4_orders_2 @ X23)
% 14.48/14.67          | ~ (v7_waybel_0 @ X23)
% 14.48/14.67          | ~ (l1_waybel_0 @ X23 @ X24)
% 14.48/14.67          | ~ (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 14.48/14.67          | (r3_waybel_9 @ X24 @ X23 @ X25)
% 14.48/14.67          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 14.48/14.67          | ~ (l1_pre_topc @ X24)
% 14.48/14.67          | ~ (v2_pre_topc @ X24)
% 14.48/14.67          | (v2_struct_0 @ X24))),
% 14.48/14.67      inference('cnf', [status(esa)], [t29_waybel_9])).
% 14.48/14.67  thf('345', plain,
% 14.48/14.67      ((((v2_struct_0 @ sk_A)
% 14.48/14.67         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | ~ (m1_subset_1 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68              (u1_struct_0 @ sk_A))
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['343', '344'])).
% 14.48/14.68  thf('346', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('347', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('348', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (m1_subset_1 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68              (u1_struct_0 @ sk_A))
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['345', '346', '347'])).
% 14.48/14.68  thf('349', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (m1_subset_1 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68              (u1_struct_0 @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['348'])).
% 14.48/14.68  thf('350', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['272', '349'])).
% 14.48/14.68  thf('351', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['350'])).
% 14.48/14.68  thf('352', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['257', '351'])).
% 14.48/14.68  thf('353', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['352'])).
% 14.48/14.68  thf('354', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['256', '353'])).
% 14.48/14.68  thf('355', plain,
% 14.48/14.68      (((~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['354'])).
% 14.48/14.68  thf('356', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['255', '355'])).
% 14.48/14.68  thf('357', plain,
% 14.48/14.68      ((((r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 14.48/14.68          (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['356'])).
% 14.48/14.68  thf('358', plain,
% 14.48/14.68      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (m1_subset_1 @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            (u1_struct_0 @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['271'])).
% 14.48/14.68  thf(t31_waybel_9, axiom,
% 14.48/14.68    (![A:$i]:
% 14.48/14.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 14.48/14.68       ( ![B:$i]:
% 14.48/14.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 14.48/14.68             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 14.48/14.68           ( ![C:$i]:
% 14.48/14.68             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 14.48/14.68               ( ![D:$i]:
% 14.48/14.68                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 14.48/14.68                   ( ( r3_waybel_9 @ A @ C @ D ) => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 14.48/14.68  thf('359', plain,
% 14.48/14.68      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 14.48/14.68         ((v2_struct_0 @ X26)
% 14.48/14.68          | ~ (v4_orders_2 @ X26)
% 14.48/14.68          | ~ (v7_waybel_0 @ X26)
% 14.48/14.68          | ~ (l1_waybel_0 @ X26 @ X27)
% 14.48/14.68          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 14.48/14.68          | (r3_waybel_9 @ X27 @ X26 @ X28)
% 14.48/14.68          | ~ (r3_waybel_9 @ X27 @ X29 @ X28)
% 14.48/14.68          | ~ (m2_yellow_6 @ X29 @ X27 @ X26)
% 14.48/14.68          | ~ (l1_pre_topc @ X27)
% 14.48/14.68          | ~ (v2_pre_topc @ X27)
% 14.48/14.68          | (v2_struct_0 @ X27))),
% 14.48/14.68      inference('cnf', [status(esa)], [t31_waybel_9])).
% 14.48/14.68  thf('360', plain,
% 14.48/14.68      ((![X0 : $i, X1 : $i]:
% 14.48/14.68          ((v2_struct_0 @ sk_A)
% 14.48/14.68           | (v1_compts_1 @ sk_A)
% 14.48/14.68           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68           | (v2_struct_0 @ sk_A)
% 14.48/14.68           | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68           | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 14.48/14.68           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 14.48/14.68                (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | (r3_waybel_9 @ sk_A @ X0 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.68           | ~ (v7_waybel_0 @ X0)
% 14.48/14.68           | ~ (v4_orders_2 @ X0)
% 14.48/14.68           | (v2_struct_0 @ X0)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['358', '359'])).
% 14.48/14.68  thf('361', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('362', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('363', plain,
% 14.48/14.68      ((![X0 : $i, X1 : $i]:
% 14.48/14.68          ((v2_struct_0 @ sk_A)
% 14.48/14.68           | (v1_compts_1 @ sk_A)
% 14.48/14.68           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68           | (v2_struct_0 @ sk_A)
% 14.48/14.68           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 14.48/14.68           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 14.48/14.68                (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | (r3_waybel_9 @ sk_A @ X0 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.68           | ~ (v7_waybel_0 @ X0)
% 14.48/14.68           | ~ (v4_orders_2 @ X0)
% 14.48/14.68           | (v2_struct_0 @ X0)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['360', '361', '362'])).
% 14.48/14.68  thf('364', plain,
% 14.48/14.68      ((![X0 : $i, X1 : $i]:
% 14.48/14.68          ((v2_struct_0 @ X0)
% 14.48/14.68           | ~ (v4_orders_2 @ X0)
% 14.48/14.68           | ~ (v7_waybel_0 @ X0)
% 14.48/14.68           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.68           | (r3_waybel_9 @ sk_A @ X0 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 14.48/14.68                (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 14.48/14.68           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68           | (v1_compts_1 @ sk_A)
% 14.48/14.68           | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['363'])).
% 14.48/14.68  thf('365', plain,
% 14.48/14.68      ((![X0 : $i]:
% 14.48/14.68          ((v2_struct_0 @ sk_A)
% 14.48/14.68           | (v1_compts_1 @ sk_A)
% 14.48/14.68           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68           | (r2_hidden @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68              k1_xboole_0)
% 14.48/14.68           | (v2_struct_0 @ sk_A)
% 14.48/14.68           | (v1_compts_1 @ sk_A)
% 14.48/14.68           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68           | ~ (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 14.48/14.68           | (r3_waybel_9 @ sk_A @ X0 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.68           | ~ (v7_waybel_0 @ X0)
% 14.48/14.68           | ~ (v4_orders_2 @ X0)
% 14.48/14.68           | (v2_struct_0 @ X0)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['357', '364'])).
% 14.48/14.68  thf('366', plain,
% 14.48/14.68      ((![X0 : $i]:
% 14.48/14.68          ((v2_struct_0 @ X0)
% 14.48/14.68           | ~ (v4_orders_2 @ X0)
% 14.48/14.68           | ~ (v7_waybel_0 @ X0)
% 14.48/14.68           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 14.48/14.68           | (r3_waybel_9 @ sk_A @ X0 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68           | ~ (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 14.48/14.68           | (r2_hidden @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68              k1_xboole_0)
% 14.48/14.68           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68           | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68           | (v1_compts_1 @ sk_A)
% 14.48/14.68           | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['365'])).
% 14.48/14.68  thf('367', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['254', '366'])).
% 14.48/14.68  thf('368', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['367'])).
% 14.48/14.68  thf('369', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['253', '368'])).
% 14.48/14.68  thf('370', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('371', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('372', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['369', '370', '371'])).
% 14.48/14.68  thf('373', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['372'])).
% 14.48/14.68  thf('374', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['252', '373'])).
% 14.48/14.68  thf('375', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('376', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('377', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['374', '375', '376'])).
% 14.48/14.68  thf('378', plain,
% 14.48/14.68      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['377'])).
% 14.48/14.68  thf('379', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['251', '378'])).
% 14.48/14.68  thf('380', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('381', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('382', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['379', '380', '381'])).
% 14.48/14.68  thf('383', plain,
% 14.48/14.68      ((((r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68          (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['382'])).
% 14.48/14.68  thf('384', plain,
% 14.48/14.68      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (m1_subset_1 @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            (u1_struct_0 @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['271'])).
% 14.48/14.68  thf('385', plain,
% 14.48/14.68      (![X33 : $i, X34 : $i]:
% 14.48/14.68         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 14.48/14.68          | ~ (r3_waybel_9 @ X33 @ (sk_B @ X33) @ X34)
% 14.48/14.68          | (v1_compts_1 @ X33)
% 14.48/14.68          | ~ (l1_pre_topc @ X33)
% 14.48/14.68          | ~ (v2_pre_topc @ X33)
% 14.48/14.68          | (v2_struct_0 @ X33))),
% 14.48/14.68      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.68  thf('386', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['384', '385'])).
% 14.48/14.68  thf('387', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('388', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('389', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['386', '387', '388'])).
% 14.48/14.68  thf('390', plain,
% 14.48/14.68      (((~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['389'])).
% 14.48/14.68  thf('391', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (r2_hidden @ 
% 14.48/14.68            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68            k1_xboole_0)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['383', '390'])).
% 14.48/14.68  thf('392', plain,
% 14.48/14.68      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 14.48/14.68          k1_xboole_0)
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['391'])).
% 14.48/14.68  thf('393', plain,
% 14.48/14.68      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 14.48/14.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 14.48/14.68  thf('394', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 14.48/14.68         | ~ (r1_tarski @ k1_xboole_0 @ 
% 14.48/14.68              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['392', '393'])).
% 14.48/14.68  thf('395', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 14.48/14.68      inference('sup-', [status(thm)], ['115', '116'])).
% 14.48/14.68  thf('396', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['394', '395'])).
% 14.48/14.68  thf('397', plain,
% 14.48/14.68      (![X21 : $i, X22 : $i]:
% 14.48/14.68         ((v2_struct_0 @ X21)
% 14.48/14.68          | ~ (v4_orders_2 @ X21)
% 14.48/14.68          | ~ (v7_waybel_0 @ X21)
% 14.48/14.68          | ~ (l1_waybel_0 @ X21 @ X22)
% 14.48/14.68          | ~ (v3_yellow_6 @ X21 @ X22)
% 14.48/14.68          | ((k10_yellow_6 @ X22 @ X21) != (k1_xboole_0))
% 14.48/14.68          | ~ (l1_pre_topc @ X22)
% 14.48/14.68          | ~ (v2_pre_topc @ X22)
% 14.48/14.68          | (v2_struct_0 @ X22))),
% 14.48/14.68      inference('cnf', [status(esa)], [d19_yellow_6])).
% 14.48/14.68  thf('398', plain,
% 14.48/14.68      (((((k1_xboole_0) != (k1_xboole_0))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['396', '397'])).
% 14.48/14.68  thf('399', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('400', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('401', plain,
% 14.48/14.68      (((((k1_xboole_0) != (k1_xboole_0))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['398', '399', '400'])).
% 14.48/14.68  thf('402', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['401'])).
% 14.48/14.68  thf('403', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['250', '402'])).
% 14.48/14.68  thf('404', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['403'])).
% 14.48/14.68  thf('405', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['226', '404'])).
% 14.48/14.68  thf('406', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['405'])).
% 14.48/14.68  thf('407', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['208', '406'])).
% 14.48/14.68  thf('408', plain,
% 14.48/14.68      (((~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['407'])).
% 14.48/14.68  thf('409', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['184', '408'])).
% 14.48/14.68  thf('410', plain,
% 14.48/14.68      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['409'])).
% 14.48/14.68  thf('411', plain,
% 14.48/14.68      (![X33 : $i]:
% 14.48/14.68         ((l1_waybel_0 @ (sk_B @ X33) @ X33)
% 14.48/14.68          | (v1_compts_1 @ X33)
% 14.48/14.68          | ~ (l1_pre_topc @ X33)
% 14.48/14.68          | ~ (v2_pre_topc @ X33)
% 14.48/14.68          | (v2_struct_0 @ X33))),
% 14.48/14.68      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.68  thf('412', plain,
% 14.48/14.68      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['163'])).
% 14.48/14.68  thf('413', plain,
% 14.48/14.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 14.48/14.68         (~ (l1_struct_0 @ X18)
% 14.48/14.68          | (v2_struct_0 @ X18)
% 14.48/14.68          | (v2_struct_0 @ X19)
% 14.48/14.68          | ~ (v4_orders_2 @ X19)
% 14.48/14.68          | ~ (v7_waybel_0 @ X19)
% 14.48/14.68          | ~ (l1_waybel_0 @ X19 @ X18)
% 14.48/14.68          | ~ (v2_struct_0 @ X20)
% 14.48/14.68          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 14.48/14.68      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 14.48/14.68  thf('414', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (l1_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['412', '413'])).
% 14.48/14.68  thf('415', plain, ((l1_struct_0 @ sk_A)),
% 14.48/14.68      inference('sup-', [status(thm)], ['59', '60'])).
% 14.48/14.68  thf('416', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['414', '415'])).
% 14.48/14.68  thf('417', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 14.48/14.68         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['416'])).
% 14.48/14.68  thf('418', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['411', '417'])).
% 14.48/14.68  thf('419', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('420', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('421', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['418', '419', '420'])).
% 14.48/14.68  thf('422', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['421'])).
% 14.48/14.68  thf('423', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['410', '422'])).
% 14.48/14.68  thf('424', plain,
% 14.48/14.68      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['423'])).
% 14.48/14.68  thf('425', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['143', '424'])).
% 14.48/14.68  thf('426', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('427', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('428', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['425', '426', '427'])).
% 14.48/14.68  thf('429', plain,
% 14.48/14.68      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['428'])).
% 14.48/14.68  thf('430', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['142', '429'])).
% 14.48/14.68  thf('431', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('432', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('433', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['430', '431', '432'])).
% 14.48/14.68  thf('434', plain,
% 14.48/14.68      ((((v2_struct_0 @ (sk_B @ sk_A))
% 14.48/14.68         | (v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['433'])).
% 14.48/14.68  thf('435', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('436', plain,
% 14.48/14.68      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ (sk_B @ sk_A))))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('clc', [status(thm)], ['434', '435'])).
% 14.48/14.68  thf('437', plain,
% 14.48/14.68      (![X33 : $i]:
% 14.48/14.68         (~ (v2_struct_0 @ (sk_B @ X33))
% 14.48/14.68          | (v1_compts_1 @ X33)
% 14.48/14.68          | ~ (l1_pre_topc @ X33)
% 14.48/14.68          | ~ (v2_pre_topc @ X33)
% 14.48/14.68          | (v2_struct_0 @ X33))),
% 14.48/14.68      inference('cnf', [status(esa)], [t35_yellow19])).
% 14.48/14.68  thf('438', plain,
% 14.48/14.68      ((((v1_compts_1 @ sk_A)
% 14.48/14.68         | (v2_struct_0 @ sk_A)
% 14.48/14.68         | ~ (v2_pre_topc @ sk_A)
% 14.48/14.68         | ~ (l1_pre_topc @ sk_A)
% 14.48/14.68         | (v1_compts_1 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('sup-', [status(thm)], ['436', '437'])).
% 14.48/14.68  thf('439', plain, ((v2_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('440', plain, ((l1_pre_topc @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('441', plain,
% 14.48/14.68      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('demod', [status(thm)], ['438', '439', '440'])).
% 14.48/14.68  thf('442', plain,
% 14.48/14.68      ((((v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('simplify', [status(thm)], ['441'])).
% 14.48/14.68  thf('443', plain, (~ (v2_struct_0 @ sk_A)),
% 14.48/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.48/14.68  thf('444', plain,
% 14.48/14.68      (((v1_compts_1 @ sk_A))
% 14.48/14.68         <= ((![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) & 
% 14.48/14.68             (![X37 : $i]:
% 14.48/14.68                ((v2_struct_0 @ X37)
% 14.48/14.68                 | ~ (v4_orders_2 @ X37)
% 14.48/14.68                 | ~ (v7_waybel_0 @ X37)
% 14.48/14.68                 | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68                 | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37))))),
% 14.48/14.68      inference('clc', [status(thm)], ['442', '443'])).
% 14.48/14.68  thf('445', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 14.48/14.68      inference('split', [status(esa)], ['2'])).
% 14.48/14.68  thf('446', plain,
% 14.48/14.68      (~
% 14.48/14.68       (![X37 : $i]:
% 14.48/14.68          ((v2_struct_0 @ X37)
% 14.48/14.68           | ~ (v4_orders_2 @ X37)
% 14.48/14.68           | ~ (v7_waybel_0 @ X37)
% 14.48/14.68           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68           | (v3_yellow_6 @ (sk_C_1 @ X37) @ sk_A))) | 
% 14.48/14.68       ((v1_compts_1 @ sk_A)) | 
% 14.48/14.68       ~
% 14.48/14.68       (![X37 : $i]:
% 14.48/14.68          ((v2_struct_0 @ X37)
% 14.48/14.68           | ~ (v4_orders_2 @ X37)
% 14.48/14.68           | ~ (v7_waybel_0 @ X37)
% 14.48/14.68           | ~ (l1_waybel_0 @ X37 @ sk_A)
% 14.48/14.68           | (m2_yellow_6 @ (sk_C_1 @ X37) @ sk_A @ X37)))),
% 14.48/14.68      inference('sup-', [status(thm)], ['444', '445'])).
% 14.48/14.68  thf('447', plain, ($false),
% 14.48/14.68      inference('sat_resolution*', [status(thm)],
% 14.48/14.68                ['1', '3', '5', '7', '9', '11', '140', '141', '446'])).
% 14.48/14.68  
% 14.48/14.68  % SZS output end Refutation
% 14.48/14.68  
% 14.48/14.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
