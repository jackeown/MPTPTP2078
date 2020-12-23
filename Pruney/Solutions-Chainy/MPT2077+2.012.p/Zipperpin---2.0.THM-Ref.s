%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1GnDPl79ID

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:59 EST 2020

% Result     : Theorem 13.59s
% Output     : Refutation 13.59s
% Verified   : 
% Statistics : Number of formulae       :  490 (4137 expanded)
%              Number of leaves         :   41 (1114 expanded)
%              Depth                    :  108
%              Number of atoms          : 11979 (88057 expanded)
%              Number of equality atoms :   84 ( 124 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X33: $i] :
      ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
      | ~ ( v3_yellow_6 @ X33 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X33: $i] :
        ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
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
    ! [X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A )
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
    ! [X30: $i,X32: $i] :
      ( ~ ( v1_compts_1 @ X30 )
      | ( r3_waybel_9 @ X30 @ X32 @ ( sk_C @ X32 @ X30 ) )
      | ~ ( l1_waybel_0 @ X32 @ X30 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
    ! [X30: $i,X32: $i] :
      ( ~ ( v1_compts_1 @ X30 )
      | ( m1_subset_1 @ ( sk_C @ X32 @ X30 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_waybel_0 @ X32 @ X30 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ( m2_yellow_6 @ ( sk_D_1 @ X29 @ X27 @ X28 ) @ X28 @ X27 )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v4_orders_2 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
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
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v7_waybel_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( l1_waybel_0 @ X17 @ X15 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( ( k10_yellow_6 @ X19 @ X18 )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v4_orders_2 @ X27 )
      | ~ ( v7_waybel_0 @ X27 )
      | ~ ( l1_waybel_0 @ X27 @ X28 )
      | ( r2_hidden @ X29 @ ( k10_yellow_6 @ X28 @ ( sk_D_1 @ X29 @ X27 @ X28 ) ) )
      | ~ ( r3_waybel_9 @ X28 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
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
    ( ! [X33: $i] :
        ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
   <= ! [X33: $i] :
        ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X33 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('120',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( ! [X33: $i] :
          ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
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
   <= ( ! [X33: $i] :
          ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ! [X33: $i] :
          ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
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
   <= ( ! [X33: $i] :
          ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ~ ( v2_struct_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
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
   <= ( ! [X33: $i] :
          ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
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
    | ~ ! [X33: $i] :
          ( ~ ( m2_yellow_6 @ X33 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X33 @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('140',plain,(
    ! [X30: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('141',plain,(
    ! [X30: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('142',plain,(
    ! [X30: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('143',plain,(
    ! [X30: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('144',plain,(
    ! [X30: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('145',plain,(
    ! [X30: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('146',plain,(
    ! [X30: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('147',plain,(
    ! [X30: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('148',plain,
    ( ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v7_waybel_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('164',plain,
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ! [X30: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('184',plain,(
    ! [X30: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('185',plain,(
    ! [X30: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('186',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('187',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( v4_orders_2 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('188',plain,
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('190',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X30: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('208',plain,(
    ! [X30: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('209',plain,(
    ! [X30: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('210',plain,
    ( ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('211',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X30: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('226',plain,(
    ! [X30: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('227',plain,(
    ! [X30: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('228',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('229',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ( l1_waybel_0 @ X17 @ X15 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('230',plain,
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('232',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X30: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('250',plain,(
    ! [X30: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('251',plain,(
    ! [X30: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('252',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('253',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('254',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('255',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('256',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('257',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('258',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('259',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('260',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('261',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( X9
        = ( k10_yellow_6 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['258','263'])).

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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['257','268'])).

thf('270',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['256','270'])).

thf('272',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('274',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('275',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('276',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('277',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('278',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('279',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('280',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('281',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('282',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('283',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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

thf('284',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['285','286','287'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['282','289'])).

thf('291',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['281','291'])).

thf('293',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ( X9
       != ( k10_yellow_6 @ X8 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ( m1_connsp_2 @ ( sk_E_1 @ X11 @ X7 @ X8 ) @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('295',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X8 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ( m1_connsp_2 @ ( sk_E_1 @ X11 @ X7 @ X8 ) @ X8 @ X11 )
      | ( r2_hidden @ X11 @ ( k10_yellow_6 @ X8 @ X7 ) )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('310',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X9 )
      | ( r1_waybel_0 @ X8 @ X7 @ X10 )
      | ~ ( m1_connsp_2 @ X10 @ X8 @ ( sk_D @ X9 @ X7 @ X8 ) )
      | ( X9
        = ( k10_yellow_6 @ X8 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('324',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['181'])).

thf('325',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('326',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('327',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ( X9
       != ( k10_yellow_6 @ X8 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r1_waybel_0 @ X8 @ X7 @ ( sk_E_1 @ X11 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_yellow_6])).

thf('328',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( k10_yellow_6 @ X8 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_waybel_0 @ X8 @ X7 @ ( sk_E_1 @ X11 @ X7 @ X8 ) )
      | ( r2_hidden @ X11 @ ( k10_yellow_6 @ X8 @ X7 ) )
      | ~ ( l1_waybel_0 @ X7 @ X8 )
      | ~ ( v7_waybel_0 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v7_waybel_0 @ X20 )
      | ~ ( l1_waybel_0 @ X20 @ X21 )
      | ~ ( r2_hidden @ X22 @ ( k10_yellow_6 @ X21 @ X20 ) )
      | ( r3_waybel_9 @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['255','351'])).

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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['254','353'])).

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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['253','355'])).

thf('357',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( l1_waybel_0 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( r3_waybel_9 @ X24 @ X23 @ X25 )
      | ~ ( r3_waybel_9 @ X24 @ X26 @ X25 )
      | ~ ( m2_yellow_6 @ X26 @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['252','366'])).

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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['251','368'])).

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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['250','373'])).

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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['249','378'])).

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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['382'])).

thf('384',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('385',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r3_waybel_9 @ X30 @ ( sk_B @ X30 ) @ X31 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['386','387','388'])).

thf('390',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['383','390'])).

thf('392',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['391'])).

thf('393',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('394',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['392','393'])).

thf('395',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('396',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['394','395'])).

thf('397',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( v3_yellow_6 @ X18 @ X19 )
      | ( ( k10_yellow_6 @ X19 @ X18 )
       != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['248','402'])).

thf('404',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference('sup-',[status(thm)],['224','404'])).

thf('406',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
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
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference('sup-',[status(thm)],['206','406'])).

thf('408',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['407'])).

thf('409',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference('sup-',[status(thm)],['182','408'])).

thf('410',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['409'])).

thf('411',plain,(
    ! [X30: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X30 ) @ X30 )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('412',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('413',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v7_waybel_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X15 )
      | ~ ( v2_struct_0 @ X17 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X16 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['414','415'])).

thf('417',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference(demod,[status(thm)],['418','419','420'])).

thf('422',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X34: $i] :
        ( ( v2_struct_0 @ X34 )
        | ~ ( v4_orders_2 @ X34 )
        | ~ ( v7_waybel_0 @ X34 )
        | ~ ( l1_waybel_0 @ X34 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
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
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference('sup-',[status(thm)],['410','422'])).

thf('424',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
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
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference('sup-',[status(thm)],['141','424'])).

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
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(demod,[status(thm)],['425','426','427'])).

thf('429',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['428'])).

thf('430',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference('sup-',[status(thm)],['140','429'])).

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
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(demod,[status(thm)],['430','431','432'])).

thf('434',plain,
    ( ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['433'])).

thf('435',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('436',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(clc,[status(thm)],['434','435'])).

thf('437',plain,(
    ! [X30: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X30 ) )
      | ( v1_compts_1 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('438',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
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
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('442',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['441'])).

thf('443',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
      & ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ) ),
    inference(clc,[status(thm)],['442','443'])).

thf('445',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('446',plain,
    ( ~ ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ~ ! [X34: $i] :
          ( ( v2_struct_0 @ X34 )
          | ~ ( v4_orders_2 @ X34 )
          | ~ ( v7_waybel_0 @ X34 )
          | ~ ( l1_waybel_0 @ X34 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X34 ) @ sk_A @ X34 ) ) ),
    inference('sup-',[status(thm)],['444','445'])).

thf('447',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','138','139','446'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1GnDPl79ID
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:45:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 13.59/13.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.59/13.80  % Solved by: fo/fo7.sh
% 13.59/13.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.59/13.80  % done 12959 iterations in 13.324s
% 13.59/13.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.59/13.80  % SZS output start Refutation
% 13.59/13.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.59/13.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 13.59/13.80  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 13.59/13.80  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 13.59/13.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 13.59/13.80  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 13.59/13.80  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 13.59/13.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.59/13.80  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 13.59/13.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.59/13.80  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 13.59/13.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 13.59/13.80  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 13.59/13.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.59/13.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 13.59/13.80  thf(sk_A_type, type, sk_A: $i).
% 13.59/13.80  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 13.59/13.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.59/13.80  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 13.59/13.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.59/13.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 13.59/13.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 13.59/13.80  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 13.59/13.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 13.59/13.80  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 13.59/13.80  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 13.59/13.80  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 13.59/13.80  thf(sk_B_type, type, sk_B: $i > $i).
% 13.59/13.80  thf(t37_yellow19, conjecture,
% 13.59/13.80    (![A:$i]:
% 13.59/13.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.59/13.80       ( ( v1_compts_1 @ A ) <=>
% 13.59/13.80         ( ![B:$i]:
% 13.59/13.80           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.80               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80             ( ?[C:$i]:
% 13.59/13.80               ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ))).
% 13.59/13.80  thf(zf_stmt_0, negated_conjecture,
% 13.59/13.80    (~( ![A:$i]:
% 13.59/13.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 13.59/13.80            ( l1_pre_topc @ A ) ) =>
% 13.59/13.80          ( ( v1_compts_1 @ A ) <=>
% 13.59/13.80            ( ![B:$i]:
% 13.59/13.80              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.80                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80                ( ?[C:$i]:
% 13.59/13.80                  ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ) )),
% 13.59/13.80    inference('cnf.neg', [status(esa)], [t37_yellow19])).
% 13.59/13.80  thf('0', plain,
% 13.59/13.80      (![X34 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X34)
% 13.59/13.80          | ~ (v4_orders_2 @ X34)
% 13.59/13.80          | ~ (v7_waybel_0 @ X34)
% 13.59/13.80          | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80          | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34)
% 13.59/13.80          | (v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('1', plain,
% 13.59/13.80      ((![X34 : $i]:
% 13.59/13.80          ((v2_struct_0 @ X34)
% 13.59/13.80           | ~ (v4_orders_2 @ X34)
% 13.59/13.80           | ~ (v7_waybel_0 @ X34)
% 13.59/13.80           | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80           | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))) | 
% 13.59/13.80       ((v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('split', [status(esa)], ['0'])).
% 13.59/13.80  thf('2', plain,
% 13.59/13.80      (![X33 : $i]:
% 13.59/13.80         (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1)
% 13.59/13.80          | ~ (v3_yellow_6 @ X33 @ sk_A)
% 13.59/13.80          | ~ (v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('3', plain,
% 13.59/13.80      ((![X33 : $i]:
% 13.59/13.80          (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X33 @ sk_A))) | 
% 13.59/13.80       ~ ((v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('split', [status(esa)], ['2'])).
% 13.59/13.80  thf('4', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('5', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('6', plain, (((v7_waybel_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('7', plain, (((v7_waybel_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('8', plain, (((v4_orders_2 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('9', plain, (((v4_orders_2 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('10', plain, ((~ (v2_struct_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('11', plain, (~ ((v2_struct_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('split', [status(esa)], ['10'])).
% 13.59/13.80  thf('12', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('13', plain,
% 13.59/13.80      (![X34 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X34)
% 13.59/13.80          | ~ (v4_orders_2 @ X34)
% 13.59/13.80          | ~ (v7_waybel_0 @ X34)
% 13.59/13.80          | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80          | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A)
% 13.59/13.80          | (v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('14', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['13'])).
% 13.59/13.80  thf('15', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('16', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf(t35_yellow19, axiom,
% 13.59/13.80    (![A:$i]:
% 13.59/13.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.59/13.80       ( ( v1_compts_1 @ A ) <=>
% 13.59/13.80         ( ![B:$i]:
% 13.59/13.80           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.80               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80             ( ?[C:$i]:
% 13.59/13.80               ( ( r3_waybel_9 @ A @ B @ C ) & 
% 13.59/13.80                 ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 13.59/13.80  thf('17', plain,
% 13.59/13.80      (![X30 : $i, X32 : $i]:
% 13.59/13.80         (~ (v1_compts_1 @ X30)
% 13.59/13.80          | (r3_waybel_9 @ X30 @ X32 @ (sk_C @ X32 @ X30))
% 13.59/13.80          | ~ (l1_waybel_0 @ X32 @ X30)
% 13.59/13.80          | ~ (v7_waybel_0 @ X32)
% 13.59/13.80          | ~ (v4_orders_2 @ X32)
% 13.59/13.80          | (v2_struct_0 @ X32)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('18', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['16', '17'])).
% 13.59/13.80  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('21', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('demod', [status(thm)], ['18', '19', '20'])).
% 13.59/13.80  thf('22', plain,
% 13.59/13.80      (((~ (v1_compts_1 @ sk_A)
% 13.59/13.80         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['15', '21'])).
% 13.59/13.80  thf('23', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['14', '22'])).
% 13.59/13.80  thf('24', plain,
% 13.59/13.80      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['12', '23'])).
% 13.59/13.80  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('26', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['24', '25'])).
% 13.59/13.80  thf('27', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('28', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['13'])).
% 13.59/13.80  thf('29', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('30', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('31', plain,
% 13.59/13.80      (![X30 : $i, X32 : $i]:
% 13.59/13.80         (~ (v1_compts_1 @ X30)
% 13.59/13.80          | (m1_subset_1 @ (sk_C @ X32 @ X30) @ (u1_struct_0 @ X30))
% 13.59/13.80          | ~ (l1_waybel_0 @ X32 @ X30)
% 13.59/13.80          | ~ (v7_waybel_0 @ X32)
% 13.59/13.80          | ~ (v4_orders_2 @ X32)
% 13.59/13.80          | (v2_struct_0 @ X32)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('32', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 13.59/13.80         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['30', '31'])).
% 13.59/13.80  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('35', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 13.59/13.80         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('demod', [status(thm)], ['32', '33', '34'])).
% 13.59/13.80  thf('36', plain,
% 13.59/13.80      (((~ (v1_compts_1 @ sk_A)
% 13.59/13.80         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['29', '35'])).
% 13.59/13.80  thf('37', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['28', '36'])).
% 13.59/13.80  thf('38', plain,
% 13.59/13.80      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['27', '37'])).
% 13.59/13.80  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('40', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['38', '39'])).
% 13.59/13.80  thf(t32_waybel_9, axiom,
% 13.59/13.80    (![A:$i]:
% 13.59/13.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.59/13.80       ( ![B:$i]:
% 13.59/13.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.80             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80           ( ![C:$i]:
% 13.59/13.80             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 13.59/13.80               ( ~( ( r3_waybel_9 @ A @ B @ C ) & 
% 13.59/13.80                    ( ![D:$i]:
% 13.59/13.80                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 13.59/13.80                        ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 13.59/13.80  thf('41', plain,
% 13.59/13.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X27)
% 13.59/13.80          | ~ (v4_orders_2 @ X27)
% 13.59/13.80          | ~ (v7_waybel_0 @ X27)
% 13.59/13.80          | ~ (l1_waybel_0 @ X27 @ X28)
% 13.59/13.80          | (m2_yellow_6 @ (sk_D_1 @ X29 @ X27 @ X28) @ X28 @ X27)
% 13.59/13.80          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 13.59/13.80          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 13.59/13.80          | ~ (l1_pre_topc @ X28)
% 13.59/13.80          | ~ (v2_pre_topc @ X28)
% 13.59/13.80          | (v2_struct_0 @ X28))),
% 13.59/13.80      inference('cnf', [status(esa)], [t32_waybel_9])).
% 13.59/13.80  thf('42', plain,
% 13.59/13.80      ((![X0 : $i]:
% 13.59/13.80          ((v2_struct_0 @ sk_B_1)
% 13.59/13.80           | (v2_struct_0 @ sk_A)
% 13.59/13.80           | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80           | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 13.59/13.80              sk_A @ X0)
% 13.59/13.80           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.80           | ~ (v7_waybel_0 @ X0)
% 13.59/13.80           | ~ (v4_orders_2 @ X0)
% 13.59/13.80           | (v2_struct_0 @ X0)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['40', '41'])).
% 13.59/13.80  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('45', plain,
% 13.59/13.80      ((![X0 : $i]:
% 13.59/13.80          ((v2_struct_0 @ sk_B_1)
% 13.59/13.80           | (v2_struct_0 @ sk_A)
% 13.59/13.80           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 13.59/13.80              sk_A @ X0)
% 13.59/13.80           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.80           | ~ (v7_waybel_0 @ X0)
% 13.59/13.80           | ~ (v4_orders_2 @ X0)
% 13.59/13.80           | (v2_struct_0 @ X0)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['42', '43', '44'])).
% 13.59/13.80  thf('46', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['26', '45'])).
% 13.59/13.80  thf('47', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('48', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('49', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('50', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 13.59/13.80  thf('51', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['50'])).
% 13.59/13.80  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('53', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['51', '52'])).
% 13.59/13.80  thf(dt_m2_yellow_6, axiom,
% 13.59/13.80    (![A:$i,B:$i]:
% 13.59/13.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 13.59/13.80         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.80         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80       ( ![C:$i]:
% 13.59/13.80         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 13.59/13.80           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 13.59/13.80             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 13.59/13.80  thf('54', plain,
% 13.59/13.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.80         (~ (l1_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X16)
% 13.59/13.80          | ~ (v4_orders_2 @ X16)
% 13.59/13.80          | ~ (v7_waybel_0 @ X16)
% 13.59/13.80          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.80          | (v4_orders_2 @ X17)
% 13.59/13.80          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.80  thf('55', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['53', '54'])).
% 13.59/13.80  thf('56', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('57', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('58', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf(dt_l1_pre_topc, axiom,
% 13.59/13.80    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 13.59/13.80  thf('60', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 13.59/13.80  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.80      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.80  thf('62', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['55', '56', '57', '58', '61'])).
% 13.59/13.80  thf('63', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['62'])).
% 13.59/13.80  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('65', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['63', '64'])).
% 13.59/13.80  thf('66', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['51', '52'])).
% 13.59/13.80  thf('67', plain,
% 13.59/13.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.80         (~ (l1_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X16)
% 13.59/13.80          | ~ (v4_orders_2 @ X16)
% 13.59/13.80          | ~ (v7_waybel_0 @ X16)
% 13.59/13.80          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.80          | (v7_waybel_0 @ X17)
% 13.59/13.80          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.80  thf('68', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['66', '67'])).
% 13.59/13.80  thf('69', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('70', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('71', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.80      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.80  thf('73', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 13.59/13.80  thf('74', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['73'])).
% 13.59/13.80  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('76', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['74', '75'])).
% 13.59/13.80  thf('77', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['51', '52'])).
% 13.59/13.80  thf('78', plain,
% 13.59/13.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.80         (~ (l1_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X16)
% 13.59/13.80          | ~ (v4_orders_2 @ X16)
% 13.59/13.80          | ~ (v7_waybel_0 @ X16)
% 13.59/13.80          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.80          | (l1_waybel_0 @ X17 @ X15)
% 13.59/13.80          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.80  thf('79', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['77', '78'])).
% 13.59/13.80  thf('80', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('81', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('82', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.80      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.80  thf('84', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 13.59/13.80  thf('85', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['84'])).
% 13.59/13.80  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('87', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['85', '86'])).
% 13.59/13.80  thf(d19_yellow_6, axiom,
% 13.59/13.80    (![A:$i]:
% 13.59/13.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.59/13.80       ( ![B:$i]:
% 13.59/13.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.80             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80           ( ( v3_yellow_6 @ B @ A ) <=>
% 13.59/13.80             ( ( k10_yellow_6 @ A @ B ) != ( k1_xboole_0 ) ) ) ) ) ))).
% 13.59/13.80  thf('88', plain,
% 13.59/13.80      (![X18 : $i, X19 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X18)
% 13.59/13.80          | ~ (v4_orders_2 @ X18)
% 13.59/13.80          | ~ (v7_waybel_0 @ X18)
% 13.59/13.80          | ~ (l1_waybel_0 @ X18 @ X19)
% 13.59/13.80          | ((k10_yellow_6 @ X19 @ X18) = (k1_xboole_0))
% 13.59/13.80          | (v3_yellow_6 @ X18 @ X19)
% 13.59/13.80          | ~ (l1_pre_topc @ X19)
% 13.59/13.80          | ~ (v2_pre_topc @ X19)
% 13.59/13.80          | (v2_struct_0 @ X19))),
% 13.59/13.80      inference('cnf', [status(esa)], [d19_yellow_6])).
% 13.59/13.80  thf('89', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | ((k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['87', '88'])).
% 13.59/13.80  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('92', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | ((k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['89', '90', '91'])).
% 13.59/13.80  thf('93', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ((k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['76', '92'])).
% 13.59/13.80  thf('94', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | ((k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['93'])).
% 13.59/13.80  thf('95', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ((k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['65', '94'])).
% 13.59/13.80  thf('96', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | ((k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['95'])).
% 13.59/13.80  thf('97', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['24', '25'])).
% 13.59/13.80  thf('98', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['38', '39'])).
% 13.59/13.80  thf('99', plain,
% 13.59/13.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X27)
% 13.59/13.80          | ~ (v4_orders_2 @ X27)
% 13.59/13.80          | ~ (v7_waybel_0 @ X27)
% 13.59/13.80          | ~ (l1_waybel_0 @ X27 @ X28)
% 13.59/13.80          | (r2_hidden @ X29 @ 
% 13.59/13.80             (k10_yellow_6 @ X28 @ (sk_D_1 @ X29 @ X27 @ X28)))
% 13.59/13.80          | ~ (r3_waybel_9 @ X28 @ X27 @ X29)
% 13.59/13.80          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 13.59/13.80          | ~ (l1_pre_topc @ X28)
% 13.59/13.80          | ~ (v2_pre_topc @ X28)
% 13.59/13.80          | (v2_struct_0 @ X28))),
% 13.59/13.80      inference('cnf', [status(esa)], [t32_waybel_9])).
% 13.59/13.80  thf('100', plain,
% 13.59/13.80      ((![X0 : $i]:
% 13.59/13.80          ((v2_struct_0 @ sk_B_1)
% 13.59/13.80           | (v2_struct_0 @ sk_A)
% 13.59/13.80           | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80           | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 13.59/13.80              (k10_yellow_6 @ sk_A @ 
% 13.59/13.80               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 13.59/13.80           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.80           | ~ (v7_waybel_0 @ X0)
% 13.59/13.80           | ~ (v4_orders_2 @ X0)
% 13.59/13.80           | (v2_struct_0 @ X0)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['98', '99'])).
% 13.59/13.80  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('103', plain,
% 13.59/13.80      ((![X0 : $i]:
% 13.59/13.80          ((v2_struct_0 @ sk_B_1)
% 13.59/13.80           | (v2_struct_0 @ sk_A)
% 13.59/13.80           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 13.59/13.80              (k10_yellow_6 @ sk_A @ 
% 13.59/13.80               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 13.59/13.80           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.80           | ~ (v7_waybel_0 @ X0)
% 13.59/13.80           | ~ (v4_orders_2 @ X0)
% 13.59/13.80           | (v2_struct_0 @ X0)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['100', '101', '102'])).
% 13.59/13.80  thf('104', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 13.59/13.80         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            (k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['97', '103'])).
% 13.59/13.80  thf('105', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('106', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('107', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('108', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            (k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 13.59/13.80  thf('109', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            (k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['108'])).
% 13.59/13.80  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('111', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            (k10_yellow_6 @ sk_A @ 
% 13.59/13.80             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['109', '110'])).
% 13.59/13.80  thf(t7_ordinal1, axiom,
% 13.59/13.80    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.59/13.80  thf('112', plain,
% 13.59/13.80      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 13.59/13.80      inference('cnf', [status(esa)], [t7_ordinal1])).
% 13.59/13.80  thf('113', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (r1_tarski @ 
% 13.59/13.80              (k10_yellow_6 @ sk_A @ 
% 13.59/13.80               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) @ 
% 13.59/13.80              (sk_C @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['111', '112'])).
% 13.59/13.80  thf('114', plain,
% 13.59/13.80      (((~ (r1_tarski @ k1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['96', '113'])).
% 13.59/13.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 13.59/13.80  thf('115', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 13.59/13.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.59/13.80  thf('116', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['114', '115'])).
% 13.59/13.80  thf('117', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['116'])).
% 13.59/13.80  thf('118', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['51', '52'])).
% 13.59/13.80  thf('119', plain,
% 13.59/13.80      ((![X33 : $i]:
% 13.59/13.80          (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X33 @ sk_A)))
% 13.59/13.80         <= ((![X33 : $i]:
% 13.59/13.80                (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1)
% 13.59/13.80                 | ~ (v3_yellow_6 @ X33 @ sk_A))))),
% 13.59/13.80      inference('split', [status(esa)], ['2'])).
% 13.59/13.80  thf('120', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v3_yellow_6 @ 
% 13.59/13.80              (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ sk_A)))
% 13.59/13.80         <= ((![X33 : $i]:
% 13.59/13.80                (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1)
% 13.59/13.80                 | ~ (v3_yellow_6 @ X33 @ sk_A))) & 
% 13.59/13.80             ((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['118', '119'])).
% 13.59/13.80  thf('121', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= ((![X33 : $i]:
% 13.59/13.80                (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1)
% 13.59/13.80                 | ~ (v3_yellow_6 @ X33 @ sk_A))) & 
% 13.59/13.80             ((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['117', '120'])).
% 13.59/13.80  thf('122', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= ((![X33 : $i]:
% 13.59/13.80                (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1)
% 13.59/13.80                 | ~ (v3_yellow_6 @ X33 @ sk_A))) & 
% 13.59/13.80             ((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['121'])).
% 13.59/13.80  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('124', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= ((![X33 : $i]:
% 13.59/13.80                (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1)
% 13.59/13.80                 | ~ (v3_yellow_6 @ X33 @ sk_A))) & 
% 13.59/13.80             ((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['122', '123'])).
% 13.59/13.80  thf('125', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 13.59/13.80            sk_A @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['51', '52'])).
% 13.59/13.80  thf('126', plain,
% 13.59/13.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.80         (~ (l1_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X16)
% 13.59/13.80          | ~ (v4_orders_2 @ X16)
% 13.59/13.80          | ~ (v7_waybel_0 @ X16)
% 13.59/13.80          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.80          | ~ (v2_struct_0 @ X17)
% 13.59/13.80          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.80  thf('127', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ sk_B_1)
% 13.59/13.80         | ~ (v4_orders_2 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('sup-', [status(thm)], ['125', '126'])).
% 13.59/13.80  thf('128', plain,
% 13.59/13.80      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 13.59/13.80      inference('split', [status(esa)], ['4'])).
% 13.59/13.80  thf('129', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['6'])).
% 13.59/13.80  thf('130', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['8'])).
% 13.59/13.80  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.80      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.80  thf('132', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('demod', [status(thm)], ['127', '128', '129', '130', '131'])).
% 13.59/13.80  thf('133', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_B_1)))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('simplify', [status(thm)], ['132'])).
% 13.59/13.80  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('135', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_B_1)
% 13.59/13.80         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 13.59/13.80         <= (((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['133', '134'])).
% 13.59/13.80  thf('136', plain,
% 13.59/13.80      (((v2_struct_0 @ sk_B_1))
% 13.59/13.80         <= ((![X33 : $i]:
% 13.59/13.80                (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1)
% 13.59/13.80                 | ~ (v3_yellow_6 @ X33 @ sk_A))) & 
% 13.59/13.80             ((v1_compts_1 @ sk_A)) & 
% 13.59/13.80             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 13.59/13.80             ((v7_waybel_0 @ sk_B_1)) & 
% 13.59/13.80             ((v4_orders_2 @ sk_B_1)))),
% 13.59/13.80      inference('clc', [status(thm)], ['124', '135'])).
% 13.59/13.80  thf('137', plain,
% 13.59/13.80      ((~ (v2_struct_0 @ sk_B_1)) <= (~ ((v2_struct_0 @ sk_B_1)))),
% 13.59/13.80      inference('split', [status(esa)], ['10'])).
% 13.59/13.80  thf('138', plain,
% 13.59/13.80      (~ ((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A)) | 
% 13.59/13.80       ~
% 13.59/13.80       (![X33 : $i]:
% 13.59/13.80          (~ (m2_yellow_6 @ X33 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X33 @ sk_A))) | 
% 13.59/13.80       ~ ((v7_waybel_0 @ sk_B_1)) | ~ ((v4_orders_2 @ sk_B_1)) | 
% 13.59/13.80       ((v2_struct_0 @ sk_B_1))),
% 13.59/13.80      inference('sup-', [status(thm)], ['136', '137'])).
% 13.59/13.80  thf('139', plain,
% 13.59/13.80      ((![X34 : $i]:
% 13.59/13.80          ((v2_struct_0 @ X34)
% 13.59/13.80           | ~ (v4_orders_2 @ X34)
% 13.59/13.80           | ~ (v7_waybel_0 @ X34)
% 13.59/13.80           | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80           | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) | 
% 13.59/13.80       ((v1_compts_1 @ sk_A))),
% 13.59/13.80      inference('split', [status(esa)], ['13'])).
% 13.59/13.80  thf('140', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v7_waybel_0 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('141', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v4_orders_2 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('142', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v7_waybel_0 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('143', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v4_orders_2 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('144', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((l1_waybel_0 @ (sk_B @ X30) @ X30)
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('145', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v4_orders_2 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('146', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v7_waybel_0 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('147', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((l1_waybel_0 @ (sk_B @ X30) @ X30)
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('148', plain,
% 13.59/13.80      ((![X34 : $i]:
% 13.59/13.80          ((v2_struct_0 @ X34)
% 13.59/13.80           | ~ (v4_orders_2 @ X34)
% 13.59/13.80           | ~ (v7_waybel_0 @ X34)
% 13.59/13.80           | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80           | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('split', [status(esa)], ['0'])).
% 13.59/13.80  thf('149', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['147', '148'])).
% 13.59/13.80  thf('150', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('152', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['149', '150', '151'])).
% 13.59/13.80  thf('153', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['146', '152'])).
% 13.59/13.80  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('156', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['153', '154', '155'])).
% 13.59/13.80  thf('157', plain,
% 13.59/13.80      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['156'])).
% 13.59/13.80  thf('158', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['145', '157'])).
% 13.59/13.80  thf('159', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('161', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['158', '159', '160'])).
% 13.59/13.80  thf('162', plain,
% 13.59/13.80      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['161'])).
% 13.59/13.80  thf('163', plain,
% 13.59/13.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.80         (~ (l1_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X16)
% 13.59/13.80          | ~ (v4_orders_2 @ X16)
% 13.59/13.80          | ~ (v7_waybel_0 @ X16)
% 13.59/13.80          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.80          | (v7_waybel_0 @ X17)
% 13.59/13.80          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.80  thf('164', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['162', '163'])).
% 13.59/13.80  thf('165', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.80      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.80  thf('166', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['164', '165'])).
% 13.59/13.80  thf('167', plain,
% 13.59/13.80      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['166'])).
% 13.59/13.80  thf('168', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['144', '167'])).
% 13.59/13.80  thf('169', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('171', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['168', '169', '170'])).
% 13.59/13.80  thf('172', plain,
% 13.59/13.80      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['171'])).
% 13.59/13.80  thf('173', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['143', '172'])).
% 13.59/13.80  thf('174', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('175', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('176', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['173', '174', '175'])).
% 13.59/13.80  thf('177', plain,
% 13.59/13.80      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['176'])).
% 13.59/13.80  thf('178', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['142', '177'])).
% 13.59/13.80  thf('179', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('180', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('181', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['178', '179', '180'])).
% 13.59/13.80  thf('182', plain,
% 13.59/13.80      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['181'])).
% 13.59/13.80  thf('183', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v4_orders_2 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('184', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v7_waybel_0 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('185', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((l1_waybel_0 @ (sk_B @ X30) @ X30)
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('186', plain,
% 13.59/13.80      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['161'])).
% 13.59/13.80  thf('187', plain,
% 13.59/13.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.80         (~ (l1_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X16)
% 13.59/13.80          | ~ (v4_orders_2 @ X16)
% 13.59/13.80          | ~ (v7_waybel_0 @ X16)
% 13.59/13.80          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.80          | (v4_orders_2 @ X17)
% 13.59/13.80          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.80  thf('188', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['186', '187'])).
% 13.59/13.80  thf('189', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.80      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.80  thf('190', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['188', '189'])).
% 13.59/13.80  thf('191', plain,
% 13.59/13.80      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['190'])).
% 13.59/13.80  thf('192', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['185', '191'])).
% 13.59/13.80  thf('193', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('194', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('195', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['192', '193', '194'])).
% 13.59/13.80  thf('196', plain,
% 13.59/13.80      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['195'])).
% 13.59/13.80  thf('197', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['184', '196'])).
% 13.59/13.80  thf('198', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('199', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('200', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['197', '198', '199'])).
% 13.59/13.80  thf('201', plain,
% 13.59/13.80      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['200'])).
% 13.59/13.80  thf('202', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['183', '201'])).
% 13.59/13.80  thf('203', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('205', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['202', '203', '204'])).
% 13.59/13.80  thf('206', plain,
% 13.59/13.80      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['205'])).
% 13.59/13.80  thf('207', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v4_orders_2 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('208', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v7_waybel_0 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('209', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((l1_waybel_0 @ (sk_B @ X30) @ X30)
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('210', plain,
% 13.59/13.80      ((![X34 : $i]:
% 13.59/13.80          ((v2_struct_0 @ X34)
% 13.59/13.80           | ~ (v4_orders_2 @ X34)
% 13.59/13.80           | ~ (v7_waybel_0 @ X34)
% 13.59/13.80           | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80           | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('split', [status(esa)], ['13'])).
% 13.59/13.80  thf('211', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['209', '210'])).
% 13.59/13.80  thf('212', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('214', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('demod', [status(thm)], ['211', '212', '213'])).
% 13.59/13.80  thf('215', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['208', '214'])).
% 13.59/13.80  thf('216', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('218', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('demod', [status(thm)], ['215', '216', '217'])).
% 13.59/13.80  thf('219', plain,
% 13.59/13.80      ((((v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['218'])).
% 13.59/13.80  thf('220', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['207', '219'])).
% 13.59/13.80  thf('221', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('222', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('223', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('demod', [status(thm)], ['220', '221', '222'])).
% 13.59/13.80  thf('224', plain,
% 13.59/13.80      ((((v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['223'])).
% 13.59/13.80  thf('225', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v7_waybel_0 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('226', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v4_orders_2 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('227', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((l1_waybel_0 @ (sk_B @ X30) @ X30)
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('228', plain,
% 13.59/13.80      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['161'])).
% 13.59/13.80  thf('229', plain,
% 13.59/13.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.80         (~ (l1_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X15)
% 13.59/13.80          | (v2_struct_0 @ X16)
% 13.59/13.80          | ~ (v4_orders_2 @ X16)
% 13.59/13.80          | ~ (v7_waybel_0 @ X16)
% 13.59/13.80          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.80          | (l1_waybel_0 @ X17 @ X15)
% 13.59/13.80          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.80  thf('230', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['228', '229'])).
% 13.59/13.80  thf('231', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.80      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.80  thf('232', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['230', '231'])).
% 13.59/13.80  thf('233', plain,
% 13.59/13.80      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['232'])).
% 13.59/13.80  thf('234', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['227', '233'])).
% 13.59/13.80  thf('235', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('236', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('237', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['234', '235', '236'])).
% 13.59/13.80  thf('238', plain,
% 13.59/13.80      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['237'])).
% 13.59/13.80  thf('239', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['226', '238'])).
% 13.59/13.80  thf('240', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('242', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['239', '240', '241'])).
% 13.59/13.80  thf('243', plain,
% 13.59/13.80      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['242'])).
% 13.59/13.80  thf('244', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['225', '243'])).
% 13.59/13.80  thf('245', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('247', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['244', '245', '246'])).
% 13.59/13.80  thf('248', plain,
% 13.59/13.80      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['247'])).
% 13.59/13.80  thf('249', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v7_waybel_0 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('250', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((v4_orders_2 @ (sk_B @ X30))
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('251', plain,
% 13.59/13.80      (![X30 : $i]:
% 13.59/13.80         ((l1_waybel_0 @ (sk_B @ X30) @ X30)
% 13.59/13.80          | (v1_compts_1 @ X30)
% 13.59/13.80          | ~ (l1_pre_topc @ X30)
% 13.59/13.80          | ~ (v2_pre_topc @ X30)
% 13.59/13.80          | (v2_struct_0 @ X30))),
% 13.59/13.80      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.80  thf('252', plain,
% 13.59/13.80      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['161'])).
% 13.59/13.80  thf('253', plain,
% 13.59/13.80      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['181'])).
% 13.59/13.80  thf('254', plain,
% 13.59/13.80      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['205'])).
% 13.59/13.80  thf('255', plain,
% 13.59/13.80      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['247'])).
% 13.59/13.80  thf('256', plain,
% 13.59/13.80      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['205'])).
% 13.59/13.80  thf('257', plain,
% 13.59/13.80      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['181'])).
% 13.59/13.80  thf('258', plain,
% 13.59/13.80      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['247'])).
% 13.59/13.80  thf('259', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 13.59/13.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.59/13.80  thf(t3_subset, axiom,
% 13.59/13.80    (![A:$i,B:$i]:
% 13.59/13.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.59/13.80  thf('260', plain,
% 13.59/13.80      (![X1 : $i, X3 : $i]:
% 13.59/13.80         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 13.59/13.80      inference('cnf', [status(esa)], [t3_subset])).
% 13.59/13.80  thf('261', plain,
% 13.59/13.80      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 13.59/13.80      inference('sup-', [status(thm)], ['259', '260'])).
% 13.59/13.80  thf(d18_yellow_6, axiom,
% 13.59/13.80    (![A:$i]:
% 13.59/13.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.59/13.80       ( ![B:$i]:
% 13.59/13.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.80             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80           ( ![C:$i]:
% 13.59/13.80             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.59/13.80               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 13.59/13.80                 ( ![D:$i]:
% 13.59/13.80                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 13.59/13.80                     ( ( r2_hidden @ D @ C ) <=>
% 13.59/13.80                       ( ![E:$i]:
% 13.59/13.80                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 13.59/13.80                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 13.59/13.80  thf('262', plain,
% 13.59/13.80      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X7)
% 13.59/13.80          | ~ (v4_orders_2 @ X7)
% 13.59/13.80          | ~ (v7_waybel_0 @ X7)
% 13.59/13.80          | ~ (l1_waybel_0 @ X7 @ X8)
% 13.59/13.80          | (m1_subset_1 @ (sk_D @ X9 @ X7 @ X8) @ (u1_struct_0 @ X8))
% 13.59/13.80          | ((X9) = (k10_yellow_6 @ X8 @ X7))
% 13.59/13.80          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 13.59/13.80          | ~ (l1_pre_topc @ X8)
% 13.59/13.80          | ~ (v2_pre_topc @ X8)
% 13.59/13.80          | (v2_struct_0 @ X8))),
% 13.59/13.80      inference('cnf', [status(esa)], [d18_yellow_6])).
% 13.59/13.80  thf('263', plain,
% 13.59/13.80      (![X0 : $i, X1 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X0)
% 13.59/13.80          | ~ (v2_pre_topc @ X0)
% 13.59/13.80          | ~ (l1_pre_topc @ X0)
% 13.59/13.80          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 13.59/13.80          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ (u1_struct_0 @ X0))
% 13.59/13.80          | ~ (l1_waybel_0 @ X1 @ X0)
% 13.59/13.80          | ~ (v7_waybel_0 @ X1)
% 13.59/13.80          | ~ (v4_orders_2 @ X1)
% 13.59/13.80          | (v2_struct_0 @ X1))),
% 13.59/13.80      inference('sup-', [status(thm)], ['261', '262'])).
% 13.59/13.80  thf('264', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['258', '263'])).
% 13.59/13.80  thf('265', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('266', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('267', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['264', '265', '266'])).
% 13.59/13.80  thf('268', plain,
% 13.59/13.80      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['267'])).
% 13.59/13.80  thf('269', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['257', '268'])).
% 13.59/13.80  thf('270', plain,
% 13.59/13.80      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['269'])).
% 13.59/13.80  thf('271', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['256', '270'])).
% 13.59/13.80  thf('272', plain,
% 13.59/13.80      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['271'])).
% 13.59/13.80  thf('273', plain,
% 13.59/13.80      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['271'])).
% 13.59/13.80  thf('274', plain,
% 13.59/13.80      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['205'])).
% 13.59/13.80  thf('275', plain,
% 13.59/13.80      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['181'])).
% 13.59/13.80  thf('276', plain,
% 13.59/13.80      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['247'])).
% 13.59/13.80  thf('277', plain,
% 13.59/13.80      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.80         | (m1_subset_1 @ 
% 13.59/13.80            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.80            (u1_struct_0 @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['271'])).
% 13.59/13.80  thf('278', plain,
% 13.59/13.80      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['205'])).
% 13.59/13.80  thf('279', plain,
% 13.59/13.80      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['181'])).
% 13.59/13.80  thf('280', plain,
% 13.59/13.80      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['247'])).
% 13.59/13.80  thf('281', plain,
% 13.59/13.80      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['181'])).
% 13.59/13.80  thf('282', plain,
% 13.59/13.80      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['205'])).
% 13.59/13.80  thf('283', plain,
% 13.59/13.80      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['247'])).
% 13.59/13.80  thf(dt_k10_yellow_6, axiom,
% 13.59/13.80    (![A:$i,B:$i]:
% 13.59/13.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 13.59/13.80         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 13.59/13.80         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.80       ( m1_subset_1 @
% 13.59/13.80         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 13.59/13.80  thf('284', plain,
% 13.59/13.80      (![X13 : $i, X14 : $i]:
% 13.59/13.80         (~ (l1_pre_topc @ X13)
% 13.59/13.80          | ~ (v2_pre_topc @ X13)
% 13.59/13.80          | (v2_struct_0 @ X13)
% 13.59/13.80          | (v2_struct_0 @ X14)
% 13.59/13.80          | ~ (v4_orders_2 @ X14)
% 13.59/13.80          | ~ (v7_waybel_0 @ X14)
% 13.59/13.80          | ~ (l1_waybel_0 @ X14 @ X13)
% 13.59/13.80          | (m1_subset_1 @ (k10_yellow_6 @ X13 @ X14) @ 
% 13.59/13.80             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 13.59/13.80      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 13.59/13.80  thf('285', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.80            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.80         | ~ (l1_pre_topc @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['283', '284'])).
% 13.59/13.80  thf('286', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('287', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.80  thf('288', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.80            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('demod', [status(thm)], ['285', '286', '287'])).
% 13.59/13.80  thf('289', plain,
% 13.59/13.80      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.80            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['288'])).
% 13.59/13.80  thf('290', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.80            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['282', '289'])).
% 13.59/13.80  thf('291', plain,
% 13.59/13.80      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.80            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['290'])).
% 13.59/13.80  thf('292', plain,
% 13.59/13.80      ((((v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v2_struct_0 @ sk_A)
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.80            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('sup-', [status(thm)], ['281', '291'])).
% 13.59/13.80  thf('293', plain,
% 13.59/13.80      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.80         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.80            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.80         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.80         | (v1_compts_1 @ sk_A)
% 13.59/13.80         | (v2_struct_0 @ sk_A)))
% 13.59/13.80         <= ((![X34 : $i]:
% 13.59/13.80                ((v2_struct_0 @ X34)
% 13.59/13.80                 | ~ (v4_orders_2 @ X34)
% 13.59/13.80                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.80                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.80                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.80      inference('simplify', [status(thm)], ['292'])).
% 13.59/13.80  thf('294', plain,
% 13.59/13.80      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 13.59/13.80         ((v2_struct_0 @ X7)
% 13.59/13.81          | ~ (v4_orders_2 @ X7)
% 13.59/13.81          | ~ (v7_waybel_0 @ X7)
% 13.59/13.81          | ~ (l1_waybel_0 @ X7 @ X8)
% 13.59/13.81          | ((X9) != (k10_yellow_6 @ X8 @ X7))
% 13.59/13.81          | (r2_hidden @ X11 @ X9)
% 13.59/13.81          | (m1_connsp_2 @ (sk_E_1 @ X11 @ X7 @ X8) @ X8 @ X11)
% 13.59/13.81          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 13.59/13.81          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 13.59/13.81          | ~ (l1_pre_topc @ X8)
% 13.59/13.81          | ~ (v2_pre_topc @ X8)
% 13.59/13.81          | (v2_struct_0 @ X8))),
% 13.59/13.81      inference('cnf', [status(esa)], [d18_yellow_6])).
% 13.59/13.81  thf('295', plain,
% 13.59/13.81      (![X7 : $i, X8 : $i, X11 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X8)
% 13.59/13.81          | ~ (v2_pre_topc @ X8)
% 13.59/13.81          | ~ (l1_pre_topc @ X8)
% 13.59/13.81          | ~ (m1_subset_1 @ (k10_yellow_6 @ X8 @ X7) @ 
% 13.59/13.81               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 13.59/13.81          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 13.59/13.81          | (m1_connsp_2 @ (sk_E_1 @ X11 @ X7 @ X8) @ X8 @ X11)
% 13.59/13.81          | (r2_hidden @ X11 @ (k10_yellow_6 @ X8 @ X7))
% 13.59/13.81          | ~ (l1_waybel_0 @ X7 @ X8)
% 13.59/13.81          | ~ (v7_waybel_0 @ X7)
% 13.59/13.81          | ~ (v4_orders_2 @ X7)
% 13.59/13.81          | (v2_struct_0 @ X7))),
% 13.59/13.81      inference('simplify', [status(thm)], ['294'])).
% 13.59/13.81  thf('296', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81           | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['293', '295'])).
% 13.59/13.81  thf('297', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('298', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('299', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['296', '297', '298'])).
% 13.59/13.81  thf('300', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['299'])).
% 13.59/13.81  thf('301', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['280', '300'])).
% 13.59/13.81  thf('302', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['301'])).
% 13.59/13.81  thf('303', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['279', '302'])).
% 13.59/13.81  thf('304', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['303'])).
% 13.59/13.81  thf('305', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['278', '304'])).
% 13.59/13.81  thf('306', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              sk_A @ X0)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['305'])).
% 13.59/13.81  thf('307', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (m1_connsp_2 @ 
% 13.59/13.81            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['277', '306'])).
% 13.59/13.81  thf('308', plain,
% 13.59/13.81      ((((m1_connsp_2 @ 
% 13.59/13.81          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81          sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['307'])).
% 13.59/13.81  thf('309', plain,
% 13.59/13.81      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 13.59/13.81      inference('sup-', [status(thm)], ['259', '260'])).
% 13.59/13.81  thf('310', plain,
% 13.59/13.81      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X7)
% 13.59/13.81          | ~ (v4_orders_2 @ X7)
% 13.59/13.81          | ~ (v7_waybel_0 @ X7)
% 13.59/13.81          | ~ (l1_waybel_0 @ X7 @ X8)
% 13.59/13.81          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X9)
% 13.59/13.81          | (r1_waybel_0 @ X8 @ X7 @ X10)
% 13.59/13.81          | ~ (m1_connsp_2 @ X10 @ X8 @ (sk_D @ X9 @ X7 @ X8))
% 13.59/13.81          | ((X9) = (k10_yellow_6 @ X8 @ X7))
% 13.59/13.81          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 13.59/13.81          | ~ (l1_pre_topc @ X8)
% 13.59/13.81          | ~ (v2_pre_topc @ X8)
% 13.59/13.81          | (v2_struct_0 @ X8))),
% 13.59/13.81      inference('cnf', [status(esa)], [d18_yellow_6])).
% 13.59/13.81  thf('311', plain,
% 13.59/13.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X0)
% 13.59/13.81          | ~ (v2_pre_topc @ X0)
% 13.59/13.81          | ~ (l1_pre_topc @ X0)
% 13.59/13.81          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 13.59/13.81          | ~ (m1_connsp_2 @ X2 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0))
% 13.59/13.81          | (r1_waybel_0 @ X0 @ X1 @ X2)
% 13.59/13.81          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 13.59/13.81          | ~ (l1_waybel_0 @ X1 @ X0)
% 13.59/13.81          | ~ (v7_waybel_0 @ X1)
% 13.59/13.81          | ~ (v4_orders_2 @ X1)
% 13.59/13.81          | (v2_struct_0 @ X1))),
% 13.59/13.81      inference('sup-', [status(thm)], ['309', '310'])).
% 13.59/13.81  thf('312', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['308', '311'])).
% 13.59/13.81  thf('313', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('314', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('315', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['312', '313', '314'])).
% 13.59/13.81  thf('316', plain,
% 13.59/13.81      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['315'])).
% 13.59/13.81  thf('317', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['276', '316'])).
% 13.59/13.81  thf('318', plain,
% 13.59/13.81      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['317'])).
% 13.59/13.81  thf('319', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['275', '318'])).
% 13.59/13.81  thf('320', plain,
% 13.59/13.81      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['319'])).
% 13.59/13.81  thf('321', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81             (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['274', '320'])).
% 13.59/13.81  thf('322', plain,
% 13.59/13.81      ((((r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81           (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['321'])).
% 13.59/13.81  thf('323', plain,
% 13.59/13.81      ((((v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['205'])).
% 13.59/13.81  thf('324', plain,
% 13.59/13.81      ((((v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['181'])).
% 13.59/13.81  thf('325', plain,
% 13.59/13.81      ((((l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['247'])).
% 13.59/13.81  thf('326', plain,
% 13.59/13.81      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))) @ 
% 13.59/13.81            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['292'])).
% 13.59/13.81  thf('327', plain,
% 13.59/13.81      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X7)
% 13.59/13.81          | ~ (v4_orders_2 @ X7)
% 13.59/13.81          | ~ (v7_waybel_0 @ X7)
% 13.59/13.81          | ~ (l1_waybel_0 @ X7 @ X8)
% 13.59/13.81          | ((X9) != (k10_yellow_6 @ X8 @ X7))
% 13.59/13.81          | (r2_hidden @ X11 @ X9)
% 13.59/13.81          | ~ (r1_waybel_0 @ X8 @ X7 @ (sk_E_1 @ X11 @ X7 @ X8))
% 13.59/13.81          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 13.59/13.81          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 13.59/13.81          | ~ (l1_pre_topc @ X8)
% 13.59/13.81          | ~ (v2_pre_topc @ X8)
% 13.59/13.81          | (v2_struct_0 @ X8))),
% 13.59/13.81      inference('cnf', [status(esa)], [d18_yellow_6])).
% 13.59/13.81  thf('328', plain,
% 13.59/13.81      (![X7 : $i, X8 : $i, X11 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X8)
% 13.59/13.81          | ~ (v2_pre_topc @ X8)
% 13.59/13.81          | ~ (l1_pre_topc @ X8)
% 13.59/13.81          | ~ (m1_subset_1 @ (k10_yellow_6 @ X8 @ X7) @ 
% 13.59/13.81               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 13.59/13.81          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X8))
% 13.59/13.81          | ~ (r1_waybel_0 @ X8 @ X7 @ (sk_E_1 @ X11 @ X7 @ X8))
% 13.59/13.81          | (r2_hidden @ X11 @ (k10_yellow_6 @ X8 @ X7))
% 13.59/13.81          | ~ (l1_waybel_0 @ X7 @ X8)
% 13.59/13.81          | ~ (v7_waybel_0 @ X7)
% 13.59/13.81          | ~ (v4_orders_2 @ X7)
% 13.59/13.81          | (v2_struct_0 @ X7))),
% 13.59/13.81      inference('simplify', [status(thm)], ['327'])).
% 13.59/13.81  thf('329', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81           | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['326', '328'])).
% 13.59/13.81  thf('330', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('331', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('332', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['329', '330', '331'])).
% 13.59/13.81  thf('333', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['332'])).
% 13.59/13.81  thf('334', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['325', '333'])).
% 13.59/13.81  thf('335', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['334'])).
% 13.59/13.81  thf('336', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['324', '335'])).
% 13.59/13.81  thf('337', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['336'])).
% 13.59/13.81  thf('338', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['323', '337'])).
% 13.59/13.81  thf('339', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 13.59/13.81           | ~ (r1_waybel_0 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81                (sk_E_1 @ X0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['338'])).
% 13.59/13.81  thf('340', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ~ (m1_subset_1 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              (u1_struct_0 @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['322', '339'])).
% 13.59/13.81  thf('341', plain,
% 13.59/13.81      (((~ (m1_subset_1 @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (u1_struct_0 @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['340'])).
% 13.59/13.81  thf('342', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['273', '341'])).
% 13.59/13.81  thf('343', plain,
% 13.59/13.81      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81          k1_xboole_0)
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['342'])).
% 13.59/13.81  thf(t29_waybel_9, axiom,
% 13.59/13.81    (![A:$i]:
% 13.59/13.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.59/13.81       ( ![B:$i]:
% 13.59/13.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.81             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.81           ( ![C:$i]:
% 13.59/13.81             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 13.59/13.81               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) =>
% 13.59/13.81                 ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 13.59/13.81  thf('344', plain,
% 13.59/13.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X20)
% 13.59/13.81          | ~ (v4_orders_2 @ X20)
% 13.59/13.81          | ~ (v7_waybel_0 @ X20)
% 13.59/13.81          | ~ (l1_waybel_0 @ X20 @ X21)
% 13.59/13.81          | ~ (r2_hidden @ X22 @ (k10_yellow_6 @ X21 @ X20))
% 13.59/13.81          | (r3_waybel_9 @ X21 @ X20 @ X22)
% 13.59/13.81          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 13.59/13.81          | ~ (l1_pre_topc @ X21)
% 13.59/13.81          | ~ (v2_pre_topc @ X21)
% 13.59/13.81          | (v2_struct_0 @ X21))),
% 13.59/13.81      inference('cnf', [status(esa)], [t29_waybel_9])).
% 13.59/13.81  thf('345', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | ~ (m1_subset_1 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              (u1_struct_0 @ sk_A))
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['343', '344'])).
% 13.59/13.81  thf('346', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('347', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('348', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (m1_subset_1 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              (u1_struct_0 @ sk_A))
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['345', '346', '347'])).
% 13.59/13.81  thf('349', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (m1_subset_1 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              (u1_struct_0 @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['348'])).
% 13.59/13.81  thf('350', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['272', '349'])).
% 13.59/13.81  thf('351', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['350'])).
% 13.59/13.81  thf('352', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['255', '351'])).
% 13.59/13.81  thf('353', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['352'])).
% 13.59/13.81  thf('354', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['254', '353'])).
% 13.59/13.81  thf('355', plain,
% 13.59/13.81      (((~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['354'])).
% 13.59/13.81  thf('356', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['253', '355'])).
% 13.59/13.81  thf('357', plain,
% 13.59/13.81      ((((r3_waybel_9 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A)) @ 
% 13.59/13.81          (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['356'])).
% 13.59/13.81  thf('358', plain,
% 13.59/13.81      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (m1_subset_1 @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (u1_struct_0 @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['271'])).
% 13.59/13.81  thf(t31_waybel_9, axiom,
% 13.59/13.81    (![A:$i]:
% 13.59/13.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.59/13.81       ( ![B:$i]:
% 13.59/13.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 13.59/13.81             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 13.59/13.81           ( ![C:$i]:
% 13.59/13.81             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 13.59/13.81               ( ![D:$i]:
% 13.59/13.81                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 13.59/13.81                   ( ( r3_waybel_9 @ A @ C @ D ) => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 13.59/13.81  thf('359', plain,
% 13.59/13.81      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X23)
% 13.59/13.81          | ~ (v4_orders_2 @ X23)
% 13.59/13.81          | ~ (v7_waybel_0 @ X23)
% 13.59/13.81          | ~ (l1_waybel_0 @ X23 @ X24)
% 13.59/13.81          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 13.59/13.81          | (r3_waybel_9 @ X24 @ X23 @ X25)
% 13.59/13.81          | ~ (r3_waybel_9 @ X24 @ X26 @ X25)
% 13.59/13.81          | ~ (m2_yellow_6 @ X26 @ X24 @ X23)
% 13.59/13.81          | ~ (l1_pre_topc @ X24)
% 13.59/13.81          | ~ (v2_pre_topc @ X24)
% 13.59/13.81          | (v2_struct_0 @ X24))),
% 13.59/13.81      inference('cnf', [status(esa)], [t31_waybel_9])).
% 13.59/13.81  thf('360', plain,
% 13.59/13.81      ((![X0 : $i, X1 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81           | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 13.59/13.81           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 13.59/13.81                (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | (r3_waybel_9 @ sk_A @ X0 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.81           | ~ (v7_waybel_0 @ X0)
% 13.59/13.81           | ~ (v4_orders_2 @ X0)
% 13.59/13.81           | (v2_struct_0 @ X0)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['358', '359'])).
% 13.59/13.81  thf('361', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('362', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('363', plain,
% 13.59/13.81      ((![X0 : $i, X1 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 13.59/13.81           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 13.59/13.81                (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | (r3_waybel_9 @ sk_A @ X0 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.81           | ~ (v7_waybel_0 @ X0)
% 13.59/13.81           | ~ (v4_orders_2 @ X0)
% 13.59/13.81           | (v2_struct_0 @ X0)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['360', '361', '362'])).
% 13.59/13.81  thf('364', plain,
% 13.59/13.81      ((![X0 : $i, X1 : $i]:
% 13.59/13.81          ((v2_struct_0 @ X0)
% 13.59/13.81           | ~ (v4_orders_2 @ X0)
% 13.59/13.81           | ~ (v7_waybel_0 @ X0)
% 13.59/13.81           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.81           | (r3_waybel_9 @ sk_A @ X0 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 13.59/13.81                (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 13.59/13.81           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['363'])).
% 13.59/13.81  thf('365', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (r2_hidden @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              k1_xboole_0)
% 13.59/13.81           | (v2_struct_0 @ sk_A)
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | ~ (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 13.59/13.81           | (r3_waybel_9 @ sk_A @ X0 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.81           | ~ (v7_waybel_0 @ X0)
% 13.59/13.81           | ~ (v4_orders_2 @ X0)
% 13.59/13.81           | (v2_struct_0 @ X0)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['357', '364'])).
% 13.59/13.81  thf('366', plain,
% 13.59/13.81      ((![X0 : $i]:
% 13.59/13.81          ((v2_struct_0 @ X0)
% 13.59/13.81           | ~ (v4_orders_2 @ X0)
% 13.59/13.81           | ~ (v7_waybel_0 @ X0)
% 13.59/13.81           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 13.59/13.81           | (r3_waybel_9 @ sk_A @ X0 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81           | ~ (m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 13.59/13.81           | (r2_hidden @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81              k1_xboole_0)
% 13.59/13.81           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81           | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81           | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81           | (v1_compts_1 @ sk_A)
% 13.59/13.81           | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['365'])).
% 13.59/13.81  thf('367', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['252', '366'])).
% 13.59/13.81  thf('368', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['367'])).
% 13.59/13.81  thf('369', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['251', '368'])).
% 13.59/13.81  thf('370', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('371', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('372', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['369', '370', '371'])).
% 13.59/13.81  thf('373', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['372'])).
% 13.59/13.81  thf('374', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['250', '373'])).
% 13.59/13.81  thf('375', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('376', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('377', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['374', '375', '376'])).
% 13.59/13.81  thf('378', plain,
% 13.59/13.81      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['377'])).
% 13.59/13.81  thf('379', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['249', '378'])).
% 13.59/13.81  thf('380', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('381', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('382', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['379', '380', '381'])).
% 13.59/13.81  thf('383', plain,
% 13.59/13.81      ((((r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81          (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['382'])).
% 13.59/13.81  thf('384', plain,
% 13.59/13.81      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (m1_subset_1 @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            (u1_struct_0 @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['271'])).
% 13.59/13.81  thf('385', plain,
% 13.59/13.81      (![X30 : $i, X31 : $i]:
% 13.59/13.81         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 13.59/13.81          | ~ (r3_waybel_9 @ X30 @ (sk_B @ X30) @ X31)
% 13.59/13.81          | (v1_compts_1 @ X30)
% 13.59/13.81          | ~ (l1_pre_topc @ X30)
% 13.59/13.81          | ~ (v2_pre_topc @ X30)
% 13.59/13.81          | (v2_struct_0 @ X30))),
% 13.59/13.81      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.81  thf('386', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['384', '385'])).
% 13.59/13.81  thf('387', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('388', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('389', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['386', '387', '388'])).
% 13.59/13.81  thf('390', plain,
% 13.59/13.81      (((~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['389'])).
% 13.59/13.81  thf('391', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (r2_hidden @ 
% 13.59/13.81            (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81            k1_xboole_0)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['383', '390'])).
% 13.59/13.81  thf('392', plain,
% 13.59/13.81      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A) @ 
% 13.59/13.81          k1_xboole_0)
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['391'])).
% 13.59/13.81  thf('393', plain,
% 13.59/13.81      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 13.59/13.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 13.59/13.81  thf('394', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))
% 13.59/13.81         | ~ (r1_tarski @ k1_xboole_0 @ 
% 13.59/13.81              (sk_D @ k1_xboole_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['392', '393'])).
% 13.59/13.81  thf('395', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 13.59/13.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 13.59/13.81  thf('396', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_1 @ (sk_B @ sk_A))))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['394', '395'])).
% 13.59/13.81  thf('397', plain,
% 13.59/13.81      (![X18 : $i, X19 : $i]:
% 13.59/13.81         ((v2_struct_0 @ X18)
% 13.59/13.81          | ~ (v4_orders_2 @ X18)
% 13.59/13.81          | ~ (v7_waybel_0 @ X18)
% 13.59/13.81          | ~ (l1_waybel_0 @ X18 @ X19)
% 13.59/13.81          | ~ (v3_yellow_6 @ X18 @ X19)
% 13.59/13.81          | ((k10_yellow_6 @ X19 @ X18) != (k1_xboole_0))
% 13.59/13.81          | ~ (l1_pre_topc @ X19)
% 13.59/13.81          | ~ (v2_pre_topc @ X19)
% 13.59/13.81          | (v2_struct_0 @ X19))),
% 13.59/13.81      inference('cnf', [status(esa)], [d19_yellow_6])).
% 13.59/13.81  thf('398', plain,
% 13.59/13.81      (((((k1_xboole_0) != (k1_xboole_0))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['396', '397'])).
% 13.59/13.81  thf('399', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('400', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('401', plain,
% 13.59/13.81      (((((k1_xboole_0) != (k1_xboole_0))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['398', '399', '400'])).
% 13.59/13.81  thf('402', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['401'])).
% 13.59/13.81  thf('403', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['248', '402'])).
% 13.59/13.81  thf('404', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v3_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['403'])).
% 13.59/13.81  thf('405', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['224', '404'])).
% 13.59/13.81  thf('406', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['405'])).
% 13.59/13.81  thf('407', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['206', '406'])).
% 13.59/13.81  thf('408', plain,
% 13.59/13.81      (((~ (v7_waybel_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['407'])).
% 13.59/13.81  thf('409', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['182', '408'])).
% 13.59/13.81  thf('410', plain,
% 13.59/13.81      ((((v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['409'])).
% 13.59/13.81  thf('411', plain,
% 13.59/13.81      (![X30 : $i]:
% 13.59/13.81         ((l1_waybel_0 @ (sk_B @ X30) @ X30)
% 13.59/13.81          | (v1_compts_1 @ X30)
% 13.59/13.81          | ~ (l1_pre_topc @ X30)
% 13.59/13.81          | ~ (v2_pre_topc @ X30)
% 13.59/13.81          | (v2_struct_0 @ X30))),
% 13.59/13.81      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.81  thf('412', plain,
% 13.59/13.81      ((((m2_yellow_6 @ (sk_C_1 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['161'])).
% 13.59/13.81  thf('413', plain,
% 13.59/13.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 13.59/13.81         (~ (l1_struct_0 @ X15)
% 13.59/13.81          | (v2_struct_0 @ X15)
% 13.59/13.81          | (v2_struct_0 @ X16)
% 13.59/13.81          | ~ (v4_orders_2 @ X16)
% 13.59/13.81          | ~ (v7_waybel_0 @ X16)
% 13.59/13.81          | ~ (l1_waybel_0 @ X16 @ X15)
% 13.59/13.81          | ~ (v2_struct_0 @ X17)
% 13.59/13.81          | ~ (m2_yellow_6 @ X17 @ X15 @ X16))),
% 13.59/13.81      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 13.59/13.81  thf('414', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (l1_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['412', '413'])).
% 13.59/13.81  thf('415', plain, ((l1_struct_0 @ sk_A)),
% 13.59/13.81      inference('sup-', [status(thm)], ['59', '60'])).
% 13.59/13.81  thf('416', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['414', '415'])).
% 13.59/13.81  thf('417', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 13.59/13.81         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['416'])).
% 13.59/13.81  thf('418', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['411', '417'])).
% 13.59/13.81  thf('419', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('420', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('421', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['418', '419', '420'])).
% 13.59/13.81  thf('422', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v2_struct_0 @ (sk_C_1 @ (sk_B @ sk_A)))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['421'])).
% 13.59/13.81  thf('423', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['410', '422'])).
% 13.59/13.81  thf('424', plain,
% 13.59/13.81      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['423'])).
% 13.59/13.81  thf('425', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['141', '424'])).
% 13.59/13.81  thf('426', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('427', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('428', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['425', '426', '427'])).
% 13.59/13.81  thf('429', plain,
% 13.59/13.81      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['428'])).
% 13.59/13.81  thf('430', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['140', '429'])).
% 13.59/13.81  thf('431', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('432', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('433', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['430', '431', '432'])).
% 13.59/13.81  thf('434', plain,
% 13.59/13.81      ((((v2_struct_0 @ (sk_B @ sk_A))
% 13.59/13.81         | (v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['433'])).
% 13.59/13.81  thf('435', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('436', plain,
% 13.59/13.81      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ (sk_B @ sk_A))))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('clc', [status(thm)], ['434', '435'])).
% 13.59/13.81  thf('437', plain,
% 13.59/13.81      (![X30 : $i]:
% 13.59/13.81         (~ (v2_struct_0 @ (sk_B @ X30))
% 13.59/13.81          | (v1_compts_1 @ X30)
% 13.59/13.81          | ~ (l1_pre_topc @ X30)
% 13.59/13.81          | ~ (v2_pre_topc @ X30)
% 13.59/13.81          | (v2_struct_0 @ X30))),
% 13.59/13.81      inference('cnf', [status(esa)], [t35_yellow19])).
% 13.59/13.81  thf('438', plain,
% 13.59/13.81      ((((v1_compts_1 @ sk_A)
% 13.59/13.81         | (v2_struct_0 @ sk_A)
% 13.59/13.81         | ~ (v2_pre_topc @ sk_A)
% 13.59/13.81         | ~ (l1_pre_topc @ sk_A)
% 13.59/13.81         | (v1_compts_1 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('sup-', [status(thm)], ['436', '437'])).
% 13.59/13.81  thf('439', plain, ((v2_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('440', plain, ((l1_pre_topc @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('441', plain,
% 13.59/13.81      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('demod', [status(thm)], ['438', '439', '440'])).
% 13.59/13.81  thf('442', plain,
% 13.59/13.81      ((((v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('simplify', [status(thm)], ['441'])).
% 13.59/13.81  thf('443', plain, (~ (v2_struct_0 @ sk_A)),
% 13.59/13.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.59/13.81  thf('444', plain,
% 13.59/13.81      (((v1_compts_1 @ sk_A))
% 13.59/13.81         <= ((![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) & 
% 13.59/13.81             (![X34 : $i]:
% 13.59/13.81                ((v2_struct_0 @ X34)
% 13.59/13.81                 | ~ (v4_orders_2 @ X34)
% 13.59/13.81                 | ~ (v7_waybel_0 @ X34)
% 13.59/13.81                 | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81                 | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34))))),
% 13.59/13.81      inference('clc', [status(thm)], ['442', '443'])).
% 13.59/13.81  thf('445', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 13.59/13.81      inference('split', [status(esa)], ['2'])).
% 13.59/13.81  thf('446', plain,
% 13.59/13.81      (~
% 13.59/13.81       (![X34 : $i]:
% 13.59/13.81          ((v2_struct_0 @ X34)
% 13.59/13.81           | ~ (v4_orders_2 @ X34)
% 13.59/13.81           | ~ (v7_waybel_0 @ X34)
% 13.59/13.81           | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81           | (v3_yellow_6 @ (sk_C_1 @ X34) @ sk_A))) | 
% 13.59/13.81       ((v1_compts_1 @ sk_A)) | 
% 13.59/13.81       ~
% 13.59/13.81       (![X34 : $i]:
% 13.59/13.81          ((v2_struct_0 @ X34)
% 13.59/13.81           | ~ (v4_orders_2 @ X34)
% 13.59/13.81           | ~ (v7_waybel_0 @ X34)
% 13.59/13.81           | ~ (l1_waybel_0 @ X34 @ sk_A)
% 13.59/13.81           | (m2_yellow_6 @ (sk_C_1 @ X34) @ sk_A @ X34)))),
% 13.59/13.81      inference('sup-', [status(thm)], ['444', '445'])).
% 13.59/13.81  thf('447', plain, ($false),
% 13.59/13.81      inference('sat_resolution*', [status(thm)],
% 13.59/13.81                ['1', '3', '5', '7', '9', '11', '138', '139', '446'])).
% 13.59/13.81  
% 13.59/13.81  % SZS output end Refutation
% 13.59/13.81  
% 13.59/13.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
