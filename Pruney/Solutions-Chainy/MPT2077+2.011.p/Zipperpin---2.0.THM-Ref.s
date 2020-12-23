%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XFev1e1LZ5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:59 EST 2020

% Result     : Theorem 12.83s
% Output     : Refutation 12.85s
% Verified   : 
% Statistics : Number of formulae       :  492 (4126 expanded)
%              Number of leaves         :   43 (1111 expanded)
%              Depth                    :  108
%              Number of atoms          : 12010 (88931 expanded)
%              Number of equality atoms :   84 ( 124 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_yellow_6_type,type,(
    k6_yellow_6: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X39: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( l1_waybel_0 @ X39 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X38: $i] :
      ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
      | ~ ( v3_yellow_6 @ X38 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X38: $i] :
        ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
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
    ! [X39: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v7_waybel_0 @ X39 )
      | ~ ( l1_waybel_0 @ X39 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A )
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
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_compts_1 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X33 )
      | ( r3_waybel_9 @ X33 @ X34 @ ( sk_C @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_compts_1 @ X33 )
      | ( v2_struct_0 @ X34 )
      | ~ ( v4_orders_2 @ X34 )
      | ~ ( v7_waybel_0 @ X34 )
      | ~ ( l1_waybel_0 @ X34 @ X33 )
      | ( m1_subset_1 @ ( sk_C @ X34 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
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
    ( ! [X38: $i] :
        ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
   <= ! [X38: $i] :
        ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
        | ~ ( v3_yellow_6 @ X38 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v3_yellow_6 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( ! [X38: $i] :
          ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
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
   <= ( ! [X38: $i] :
          ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ! [X38: $i] :
          ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
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
   <= ( ! [X38: $i] :
          ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
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
   <= ( ! [X38: $i] :
          ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
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
    | ~ ! [X38: $i] :
          ( ~ ( m2_yellow_6 @ X38 @ sk_A @ sk_B_1 )
          | ~ ( v3_yellow_6 @ X38 @ sk_A ) )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
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

thf('142',plain,(
    ! [X35: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('143',plain,(
    ! [X35: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('144',plain,(
    ! [X35: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('145',plain,(
    ! [X35: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('146',plain,(
    ! [X35: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X35 ) @ X35 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('147',plain,(
    ! [X35: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('148',plain,(
    ! [X35: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('149',plain,(
    ! [X35: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X35 ) @ X35 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('150',plain,
    ( ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('168',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X35: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('186',plain,(
    ! [X35: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('187',plain,(
    ! [X35: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X35 ) @ X35 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('188',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X35: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('210',plain,(
    ! [X35: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('211',plain,(
    ! [X35: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X35 ) @ X35 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('212',plain,
    ( ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
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
      | ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X35: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('228',plain,(
    ! [X35: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('229',plain,(
    ! [X35: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X35 ) @ X35 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('230',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('234',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['236','237','238'])).

thf('240',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X35: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('252',plain,(
    ! [X35: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('253',plain,(
    ! [X35: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X35 ) @ X35 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('254',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('255',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('256',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('257',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('258',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('259',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('260',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('268',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['259','268'])).

thf('270',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('271',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['258','270'])).

thf('272',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('274',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('275',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('276',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('277',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('278',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('279',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('280',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('281',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('282',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('283',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['285','286','287'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['282','289'])).

thf('291',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['281','291'])).

thf('293',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['280','300'])).

thf('302',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['279','302'])).

thf('304',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['303'])).

thf('305',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['278','304'])).

thf('306',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['277','306'])).

thf('308',plain,
    ( ( ( m1_connsp_2 @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ sk_A @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['276','316'])).

thf('318',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['275','318'])).

thf('320',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['319'])).

thf('321',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['274','320'])).

thf('322',plain,
    ( ( ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['321'])).

thf('323',plain,
    ( ( ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('324',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('325',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('326',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['329','330','331'])).

thf('333',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
        | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['325','333'])).

thf('335',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['324','335'])).

thf('337',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['323','337'])).

thf('339',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_waybel_0 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_E_1 @ X0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
        | ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['338'])).

thf('340',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['322','339'])).

thf('341',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['340'])).

thf('342',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['273','341'])).

thf('343',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['345','346','347'])).

thf('349',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['348'])).

thf('350',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['272','349'])).

thf('351',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['257','351'])).

thf('353',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['256','353'])).

thf('355',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['354'])).

thf('356',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['255','355'])).

thf('357',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['360','361','362'])).

thf('364',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['363'])).

thf('365',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['357','364'])).

thf('366',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['365'])).

thf('367',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['254','366'])).

thf('368',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['367'])).

thf('369',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['369','370','371'])).

thf('373',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['372'])).

thf('374',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['374','375','376'])).

thf('378',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['377'])).

thf('379',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['379','380','381'])).

thf('383',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['382'])).

thf('384',plain,
    ( ( ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('385',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r3_waybel_9 @ X35 @ ( sk_B @ X35 ) @ X36 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('386',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['386','387','388'])).

thf('390',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['389'])).

thf('391',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['383','390'])).

thf('392',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['392','393'])).

thf('395',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('396',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k10_yellow_6 @ sk_A @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['396','397'])).

thf('399',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('401',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['398','399','400'])).

thf('402',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['401'])).

thf('403',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['250','402'])).

thf('404',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v3_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['403'])).

thf('405',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference('sup-',[status(thm)],['226','404'])).

thf('406',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['405'])).

thf('407',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference('sup-',[status(thm)],['208','406'])).

thf('408',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['407'])).

thf('409',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference('sup-',[status(thm)],['184','408'])).

thf('410',plain,
    ( ( ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['409'])).

thf('411',plain,(
    ! [X35: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X35 ) @ X35 )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('412',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) @ sk_A @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['412','413'])).

thf('415',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('416',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['414','415'])).

thf('417',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(simplify,[status(thm)],['416'])).

thf('418',plain,
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
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference(demod,[status(thm)],['418','419','420'])).

thf('422',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_2 @ ( sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X39: $i] :
        ( ( v2_struct_0 @ X39 )
        | ~ ( v4_orders_2 @ X39 )
        | ~ ( v7_waybel_0 @ X39 )
        | ~ ( l1_waybel_0 @ X39 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
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
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference('sup-',[status(thm)],['410','422'])).

thf('424',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
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
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
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
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(demod,[status(thm)],['425','426','427'])).

thf('429',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['428'])).

thf('430',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
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
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(demod,[status(thm)],['430','431','432'])).

thf('434',plain,
    ( ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['433'])).

thf('435',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('436',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(clc,[status(thm)],['434','435'])).

thf('437',plain,(
    ! [X35: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X35 ) )
      | ( v1_compts_1 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_yellow19])).

thf('438',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
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
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(demod,[status(thm)],['438','439','440'])).

thf('442',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['441'])).

thf('443',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('444',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
      & ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ) ),
    inference(clc,[status(thm)],['442','443'])).

thf('445',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('446',plain,
    ( ~ ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ~ ! [X39: $i] :
          ( ( v2_struct_0 @ X39 )
          | ~ ( v4_orders_2 @ X39 )
          | ~ ( v7_waybel_0 @ X39 )
          | ~ ( l1_waybel_0 @ X39 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_2 @ X39 ) @ sk_A @ X39 ) ) ),
    inference('sup-',[status(thm)],['444','445'])).

thf('447',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','9','11','140','141','446'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XFev1e1LZ5
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:01:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.83/13.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.83/13.03  % Solved by: fo/fo7.sh
% 12.83/13.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.83/13.03  % done 13055 iterations in 12.534s
% 12.83/13.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.83/13.03  % SZS output start Refutation
% 12.83/13.03  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 12.83/13.03  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 12.83/13.03  thf(sk_A_type, type, sk_A: $i).
% 12.83/13.03  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 12.83/13.03  thf(r3_waybel_9_type, type, r3_waybel_9: $i > $i > $i > $o).
% 12.83/13.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.83/13.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 12.83/13.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.83/13.03  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 12.83/13.03  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 12.83/13.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 12.83/13.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 12.83/13.03  thf(sk_B_type, type, sk_B: $i > $i).
% 12.83/13.03  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 12.83/13.03  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 12.83/13.03  thf(m2_yellow_6_type, type, m2_yellow_6: $i > $i > $i > $o).
% 12.83/13.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.83/13.03  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 12.83/13.03  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 12.83/13.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.83/13.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 12.83/13.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.83/13.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.83/13.03  thf(k6_yellow_6_type, type, k6_yellow_6: $i > $i).
% 12.83/13.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 12.83/13.03  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 12.83/13.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 12.83/13.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.83/13.03  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 12.83/13.03  thf(t37_yellow19, conjecture,
% 12.83/13.03    (![A:$i]:
% 12.83/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.83/13.03       ( ( v1_compts_1 @ A ) <=>
% 12.83/13.03         ( ![B:$i]:
% 12.83/13.03           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.83/13.03               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.83/13.03             ( ?[C:$i]:
% 12.83/13.03               ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ))).
% 12.83/13.03  thf(zf_stmt_0, negated_conjecture,
% 12.83/13.03    (~( ![A:$i]:
% 12.83/13.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 12.83/13.03            ( l1_pre_topc @ A ) ) =>
% 12.83/13.03          ( ( v1_compts_1 @ A ) <=>
% 12.83/13.03            ( ![B:$i]:
% 12.83/13.03              ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.83/13.03                  ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.83/13.03                ( ?[C:$i]:
% 12.83/13.03                  ( ( v3_yellow_6 @ C @ A ) & ( m2_yellow_6 @ C @ A @ B ) ) ) ) ) ) ) )),
% 12.83/13.03    inference('cnf.neg', [status(esa)], [t37_yellow19])).
% 12.83/13.03  thf('0', plain,
% 12.83/13.03      (![X39 : $i]:
% 12.83/13.03         ((v2_struct_0 @ X39)
% 12.83/13.03          | ~ (v4_orders_2 @ X39)
% 12.83/13.03          | ~ (v7_waybel_0 @ X39)
% 12.83/13.03          | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.83/13.03          | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39)
% 12.83/13.03          | (v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('1', plain,
% 12.83/13.03      ((![X39 : $i]:
% 12.83/13.03          ((v2_struct_0 @ X39)
% 12.83/13.03           | ~ (v4_orders_2 @ X39)
% 12.83/13.03           | ~ (v7_waybel_0 @ X39)
% 12.83/13.03           | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.83/13.03           | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))) | 
% 12.83/13.03       ((v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('split', [status(esa)], ['0'])).
% 12.83/13.03  thf('2', plain,
% 12.83/13.03      (![X38 : $i]:
% 12.83/13.03         (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1)
% 12.83/13.03          | ~ (v3_yellow_6 @ X38 @ sk_A)
% 12.83/13.03          | ~ (v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('3', plain,
% 12.83/13.03      ((![X38 : $i]:
% 12.83/13.03          (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X38 @ sk_A))) | 
% 12.83/13.03       ~ ((v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('split', [status(esa)], ['2'])).
% 12.83/13.03  thf('4', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A) | ~ (v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('5', plain, (((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('split', [status(esa)], ['4'])).
% 12.83/13.03  thf('6', plain, (((v7_waybel_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('7', plain, (((v7_waybel_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('split', [status(esa)], ['6'])).
% 12.83/13.03  thf('8', plain, (((v4_orders_2 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('9', plain, (((v4_orders_2 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('split', [status(esa)], ['8'])).
% 12.83/13.03  thf('10', plain, ((~ (v2_struct_0 @ sk_B_1) | ~ (v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('11', plain, (~ ((v2_struct_0 @ sk_B_1)) | ~ ((v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('split', [status(esa)], ['10'])).
% 12.83/13.03  thf('12', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.83/13.03      inference('split', [status(esa)], ['8'])).
% 12.83/13.03  thf('13', plain,
% 12.83/13.03      (![X39 : $i]:
% 12.83/13.03         ((v2_struct_0 @ X39)
% 12.83/13.03          | ~ (v4_orders_2 @ X39)
% 12.83/13.03          | ~ (v7_waybel_0 @ X39)
% 12.83/13.03          | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.83/13.03          | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A)
% 12.83/13.03          | (v1_compts_1 @ sk_A))),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('14', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 12.83/13.03      inference('split', [status(esa)], ['13'])).
% 12.83/13.03  thf('15', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.83/13.03      inference('split', [status(esa)], ['6'])).
% 12.83/13.03  thf('16', plain,
% 12.83/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.83/13.03      inference('split', [status(esa)], ['4'])).
% 12.83/13.03  thf(l37_yellow19, axiom,
% 12.83/13.03    (![A:$i]:
% 12.83/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.83/13.03       ( ( v1_compts_1 @ A ) =>
% 12.83/13.03         ( ![B:$i]:
% 12.83/13.03           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.83/13.03               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.83/13.03             ( ?[C:$i]:
% 12.83/13.03               ( ( r3_waybel_9 @ A @ B @ C ) & 
% 12.83/13.03                 ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 12.83/13.03  thf('17', plain,
% 12.83/13.03      (![X33 : $i, X34 : $i]:
% 12.83/13.03         (~ (v1_compts_1 @ X33)
% 12.83/13.03          | (v2_struct_0 @ X34)
% 12.83/13.03          | ~ (v4_orders_2 @ X34)
% 12.83/13.03          | ~ (v7_waybel_0 @ X34)
% 12.83/13.03          | ~ (l1_waybel_0 @ X34 @ X33)
% 12.83/13.03          | (r3_waybel_9 @ X33 @ X34 @ (sk_C @ X34 @ X33))
% 12.83/13.03          | ~ (l1_pre_topc @ X33)
% 12.83/13.03          | ~ (v2_pre_topc @ X33)
% 12.83/13.03          | (v2_struct_0 @ X33))),
% 12.83/13.03      inference('cnf', [status(esa)], [l37_yellow19])).
% 12.83/13.03  thf('18', plain,
% 12.83/13.03      ((((v2_struct_0 @ sk_A)
% 12.83/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.83/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.83/13.03         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.83/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.83/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.83/13.03         | (v2_struct_0 @ sk_B_1)
% 12.83/13.03         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.83/13.03      inference('sup-', [status(thm)], ['16', '17'])).
% 12.83/13.03  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 12.83/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.83/13.03  thf('21', plain,
% 12.83/13.03      ((((v2_struct_0 @ sk_A)
% 12.83/13.03         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.83/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.83/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.83/13.03         | (v2_struct_0 @ sk_B_1)
% 12.83/13.03         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('demod', [status(thm)], ['18', '19', '20'])).
% 12.85/13.03  thf('22', plain,
% 12.85/13.03      (((~ (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['15', '21'])).
% 12.85/13.03  thf('23', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['14', '22'])).
% 12.85/13.03  thf('24', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['12', '23'])).
% 12.85/13.03  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('26', plain,
% 12.85/13.03      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['24', '25'])).
% 12.85/13.03  thf('27', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['8'])).
% 12.85/13.03  thf('28', plain, (((v1_compts_1 @ sk_A)) <= (((v1_compts_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['13'])).
% 12.85/13.03  thf('29', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['6'])).
% 12.85/13.03  thf('30', plain,
% 12.85/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['4'])).
% 12.85/13.03  thf('31', plain,
% 12.85/13.03      (![X33 : $i, X34 : $i]:
% 12.85/13.03         (~ (v1_compts_1 @ X33)
% 12.85/13.03          | (v2_struct_0 @ X34)
% 12.85/13.03          | ~ (v4_orders_2 @ X34)
% 12.85/13.03          | ~ (v7_waybel_0 @ X34)
% 12.85/13.03          | ~ (l1_waybel_0 @ X34 @ X33)
% 12.85/13.03          | (m1_subset_1 @ (sk_C @ X34 @ X33) @ (u1_struct_0 @ X33))
% 12.85/13.03          | ~ (l1_pre_topc @ X33)
% 12.85/13.03          | ~ (v2_pre_topc @ X33)
% 12.85/13.03          | (v2_struct_0 @ X33))),
% 12.85/13.03      inference('cnf', [status(esa)], [l37_yellow19])).
% 12.85/13.03  thf('32', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['30', '31'])).
% 12.85/13.03  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('35', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v1_compts_1 @ sk_A))) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('demod', [status(thm)], ['32', '33', '34'])).
% 12.85/13.03  thf('36', plain,
% 12.85/13.03      (((~ (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((l1_waybel_0 @ sk_B_1 @ sk_A)) & ((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['29', '35'])).
% 12.85/13.03  thf('37', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['28', '36'])).
% 12.85/13.03  thf('38', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['27', '37'])).
% 12.85/13.03  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('40', plain,
% 12.85/13.03      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['38', '39'])).
% 12.85/13.03  thf(t32_waybel_9, axiom,
% 12.85/13.03    (![A:$i]:
% 12.85/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.85/13.03       ( ![B:$i]:
% 12.85/13.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.85/13.03             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.03           ( ![C:$i]:
% 12.85/13.03             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.85/13.03               ( ~( ( r3_waybel_9 @ A @ B @ C ) & 
% 12.85/13.03                    ( ![D:$i]:
% 12.85/13.03                      ( ( m2_yellow_6 @ D @ A @ B ) =>
% 12.85/13.03                        ( ~( r2_hidden @ C @ ( k10_yellow_6 @ A @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.85/13.03  thf('41', plain,
% 12.85/13.03      (![X30 : $i, X31 : $i, X32 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X30)
% 12.85/13.03          | ~ (v4_orders_2 @ X30)
% 12.85/13.03          | ~ (v7_waybel_0 @ X30)
% 12.85/13.03          | ~ (l1_waybel_0 @ X30 @ X31)
% 12.85/13.03          | (m2_yellow_6 @ (sk_D_1 @ X32 @ X30 @ X31) @ X31 @ X30)
% 12.85/13.03          | ~ (r3_waybel_9 @ X31 @ X30 @ X32)
% 12.85/13.03          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 12.85/13.03          | ~ (l1_pre_topc @ X31)
% 12.85/13.03          | ~ (v2_pre_topc @ X31)
% 12.85/13.03          | (v2_struct_0 @ X31))),
% 12.85/13.03      inference('cnf', [status(esa)], [t32_waybel_9])).
% 12.85/13.03  thf('42', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_B_1)
% 12.85/13.03           | (v2_struct_0 @ sk_A)
% 12.85/13.03           | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03           | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.03           | ~ (v7_waybel_0 @ X0)
% 12.85/13.03           | ~ (v4_orders_2 @ X0)
% 12.85/13.03           | (v2_struct_0 @ X0)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['40', '41'])).
% 12.85/13.03  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('45', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_B_1)
% 12.85/13.03           | (v2_struct_0 @ sk_A)
% 12.85/13.03           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03           | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.03           | ~ (v7_waybel_0 @ X0)
% 12.85/13.03           | ~ (v4_orders_2 @ X0)
% 12.85/13.03           | (v2_struct_0 @ X0)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['42', '43', '44'])).
% 12.85/13.03  thf('46', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['26', '45'])).
% 12.85/13.03  thf('47', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['8'])).
% 12.85/13.03  thf('48', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['6'])).
% 12.85/13.03  thf('49', plain,
% 12.85/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['4'])).
% 12.85/13.03  thf('50', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 12.85/13.03  thf('51', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['50'])).
% 12.85/13.03  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('53', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['51', '52'])).
% 12.85/13.03  thf(dt_m2_yellow_6, axiom,
% 12.85/13.03    (![A:$i,B:$i]:
% 12.85/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 12.85/13.03         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.85/13.03         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.03       ( ![C:$i]:
% 12.85/13.03         ( ( m2_yellow_6 @ C @ A @ B ) =>
% 12.85/13.03           ( ( ~( v2_struct_0 @ C ) ) & ( v4_orders_2 @ C ) & 
% 12.85/13.03             ( v7_waybel_0 @ C ) & ( l1_waybel_0 @ C @ A ) ) ) ) ))).
% 12.85/13.03  thf('54', plain,
% 12.85/13.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.03         (~ (l1_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X19)
% 12.85/13.03          | ~ (v4_orders_2 @ X19)
% 12.85/13.03          | ~ (v7_waybel_0 @ X19)
% 12.85/13.03          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.03          | (v4_orders_2 @ X20)
% 12.85/13.03          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.03  thf('55', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['53', '54'])).
% 12.85/13.03  thf('56', plain,
% 12.85/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['4'])).
% 12.85/13.03  thf('57', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['6'])).
% 12.85/13.03  thf('58', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['8'])).
% 12.85/13.03  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf(dt_l1_pre_topc, axiom,
% 12.85/13.03    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 12.85/13.03  thf('60', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 12.85/13.03  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.03      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.03  thf('62', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['55', '56', '57', '58', '61'])).
% 12.85/13.03  thf('63', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['62'])).
% 12.85/13.03  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('65', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['63', '64'])).
% 12.85/13.03  thf('66', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['51', '52'])).
% 12.85/13.03  thf('67', plain,
% 12.85/13.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.03         (~ (l1_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X19)
% 12.85/13.03          | ~ (v4_orders_2 @ X19)
% 12.85/13.03          | ~ (v7_waybel_0 @ X19)
% 12.85/13.03          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.03          | (v7_waybel_0 @ X20)
% 12.85/13.03          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.03  thf('68', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['66', '67'])).
% 12.85/13.03  thf('69', plain,
% 12.85/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['4'])).
% 12.85/13.03  thf('70', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['6'])).
% 12.85/13.03  thf('71', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['8'])).
% 12.85/13.03  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.03      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.03  thf('73', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 12.85/13.03  thf('74', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['73'])).
% 12.85/13.03  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('76', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['74', '75'])).
% 12.85/13.03  thf('77', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['51', '52'])).
% 12.85/13.03  thf('78', plain,
% 12.85/13.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.03         (~ (l1_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X19)
% 12.85/13.03          | ~ (v4_orders_2 @ X19)
% 12.85/13.03          | ~ (v7_waybel_0 @ X19)
% 12.85/13.03          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.03          | (l1_waybel_0 @ X20 @ X18)
% 12.85/13.03          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.03  thf('79', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['77', '78'])).
% 12.85/13.03  thf('80', plain,
% 12.85/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['4'])).
% 12.85/13.03  thf('81', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['6'])).
% 12.85/13.03  thf('82', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['8'])).
% 12.85/13.03  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.03      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.03  thf('84', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 12.85/13.03  thf('85', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['84'])).
% 12.85/13.03  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('87', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (l1_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['85', '86'])).
% 12.85/13.03  thf(d19_yellow_6, axiom,
% 12.85/13.03    (![A:$i]:
% 12.85/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.85/13.03       ( ![B:$i]:
% 12.85/13.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.85/13.03             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.03           ( ( v3_yellow_6 @ B @ A ) <=>
% 12.85/13.03             ( ( k10_yellow_6 @ A @ B ) != ( k1_xboole_0 ) ) ) ) ) ))).
% 12.85/13.03  thf('88', plain,
% 12.85/13.03      (![X21 : $i, X22 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X21)
% 12.85/13.03          | ~ (v4_orders_2 @ X21)
% 12.85/13.03          | ~ (v7_waybel_0 @ X21)
% 12.85/13.03          | ~ (l1_waybel_0 @ X21 @ X22)
% 12.85/13.03          | ((k10_yellow_6 @ X22 @ X21) = (k1_xboole_0))
% 12.85/13.03          | (v3_yellow_6 @ X21 @ X22)
% 12.85/13.03          | ~ (l1_pre_topc @ X22)
% 12.85/13.03          | ~ (v2_pre_topc @ X22)
% 12.85/13.03          | (v2_struct_0 @ X22))),
% 12.85/13.03      inference('cnf', [status(esa)], [d19_yellow_6])).
% 12.85/13.03  thf('89', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | ((k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['87', '88'])).
% 12.85/13.03  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('92', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | ((k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['89', '90', '91'])).
% 12.85/13.03  thf('93', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ((k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['76', '92'])).
% 12.85/13.03  thf('94', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | ((k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['93'])).
% 12.85/13.03  thf('95', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ((k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['65', '94'])).
% 12.85/13.03  thf('96', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | ((k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) = (k1_xboole_0))
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['95'])).
% 12.85/13.03  thf('97', plain,
% 12.85/13.03      ((((r3_waybel_9 @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['24', '25'])).
% 12.85/13.03  thf('98', plain,
% 12.85/13.03      ((((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['38', '39'])).
% 12.85/13.03  thf('99', plain,
% 12.85/13.03      (![X30 : $i, X31 : $i, X32 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X30)
% 12.85/13.03          | ~ (v4_orders_2 @ X30)
% 12.85/13.03          | ~ (v7_waybel_0 @ X30)
% 12.85/13.03          | ~ (l1_waybel_0 @ X30 @ X31)
% 12.85/13.03          | (r2_hidden @ X32 @ 
% 12.85/13.03             (k10_yellow_6 @ X31 @ (sk_D_1 @ X32 @ X30 @ X31)))
% 12.85/13.03          | ~ (r3_waybel_9 @ X31 @ X30 @ X32)
% 12.85/13.03          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 12.85/13.03          | ~ (l1_pre_topc @ X31)
% 12.85/13.03          | ~ (v2_pre_topc @ X31)
% 12.85/13.03          | (v2_struct_0 @ X31))),
% 12.85/13.03      inference('cnf', [status(esa)], [t32_waybel_9])).
% 12.85/13.03  thf('100', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_B_1)
% 12.85/13.03           | (v2_struct_0 @ sk_A)
% 12.85/13.03           | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03           | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.85/13.03              (k10_yellow_6 @ sk_A @ 
% 12.85/13.03               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 12.85/13.03           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.03           | ~ (v7_waybel_0 @ X0)
% 12.85/13.03           | ~ (v4_orders_2 @ X0)
% 12.85/13.03           | (v2_struct_0 @ X0)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['98', '99'])).
% 12.85/13.03  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('103', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_B_1)
% 12.85/13.03           | (v2_struct_0 @ sk_A)
% 12.85/13.03           | ~ (r3_waybel_9 @ sk_A @ X0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03           | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.85/13.03              (k10_yellow_6 @ sk_A @ 
% 12.85/13.03               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ X0 @ sk_A)))
% 12.85/13.03           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.03           | ~ (v7_waybel_0 @ X0)
% 12.85/13.03           | ~ (v4_orders_2 @ X0)
% 12.85/13.03           | (v2_struct_0 @ X0)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['100', '101', '102'])).
% 12.85/13.03  thf('104', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.85/13.03         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            (k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['97', '103'])).
% 12.85/13.03  thf('105', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['8'])).
% 12.85/13.03  thf('106', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['6'])).
% 12.85/13.03  thf('107', plain,
% 12.85/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['4'])).
% 12.85/13.03  thf('108', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            (k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 12.85/13.03  thf('109', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            (k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['108'])).
% 12.85/13.03  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('111', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            (k10_yellow_6 @ sk_A @ 
% 12.85/13.03             (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)))))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['109', '110'])).
% 12.85/13.03  thf(t7_ordinal1, axiom,
% 12.85/13.03    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.85/13.03  thf('112', plain,
% 12.85/13.03      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 12.85/13.03      inference('cnf', [status(esa)], [t7_ordinal1])).
% 12.85/13.03  thf('113', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (r1_tarski @ 
% 12.85/13.03              (k10_yellow_6 @ sk_A @ 
% 12.85/13.03               (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A)) @ 
% 12.85/13.03              (sk_C @ sk_B_1 @ sk_A))))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['111', '112'])).
% 12.85/13.03  thf('114', plain,
% 12.85/13.03      (((~ (r1_tarski @ k1_xboole_0 @ (sk_C @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['96', '113'])).
% 12.85/13.03  thf(t4_subset_1, axiom,
% 12.85/13.03    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 12.85/13.03  thf('115', plain,
% 12.85/13.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 12.85/13.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.85/13.03  thf(t3_subset, axiom,
% 12.85/13.03    (![A:$i,B:$i]:
% 12.85/13.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.85/13.03  thf('116', plain,
% 12.85/13.03      (![X1 : $i, X2 : $i]:
% 12.85/13.03         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 12.85/13.03      inference('cnf', [status(esa)], [t3_subset])).
% 12.85/13.03  thf('117', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 12.85/13.03      inference('sup-', [status(thm)], ['115', '116'])).
% 12.85/13.03  thf('118', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['114', '117'])).
% 12.85/13.03  thf('119', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v3_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['118'])).
% 12.85/13.03  thf('120', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['51', '52'])).
% 12.85/13.03  thf('121', plain,
% 12.85/13.03      ((![X38 : $i]:
% 12.85/13.03          (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X38 @ sk_A)))
% 12.85/13.03         <= ((![X38 : $i]:
% 12.85/13.03                (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1)
% 12.85/13.03                 | ~ (v3_yellow_6 @ X38 @ sk_A))))),
% 12.85/13.03      inference('split', [status(esa)], ['2'])).
% 12.85/13.03  thf('122', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v3_yellow_6 @ 
% 12.85/13.03              (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ sk_A)))
% 12.85/13.03         <= ((![X38 : $i]:
% 12.85/13.03                (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1)
% 12.85/13.03                 | ~ (v3_yellow_6 @ X38 @ sk_A))) & 
% 12.85/13.03             ((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['120', '121'])).
% 12.85/13.03  thf('123', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= ((![X38 : $i]:
% 12.85/13.03                (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1)
% 12.85/13.03                 | ~ (v3_yellow_6 @ X38 @ sk_A))) & 
% 12.85/13.03             ((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['119', '122'])).
% 12.85/13.03  thf('124', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= ((![X38 : $i]:
% 12.85/13.03                (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1)
% 12.85/13.03                 | ~ (v3_yellow_6 @ X38 @ sk_A))) & 
% 12.85/13.03             ((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['123'])).
% 12.85/13.03  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('126', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.85/13.03         <= ((![X38 : $i]:
% 12.85/13.03                (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1)
% 12.85/13.03                 | ~ (v3_yellow_6 @ X38 @ sk_A))) & 
% 12.85/13.03             ((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['124', '125'])).
% 12.85/13.03  thf('127', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (m2_yellow_6 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A) @ 
% 12.85/13.03            sk_A @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['51', '52'])).
% 12.85/13.03  thf('128', plain,
% 12.85/13.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.03         (~ (l1_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X19)
% 12.85/13.03          | ~ (v4_orders_2 @ X19)
% 12.85/13.03          | ~ (v7_waybel_0 @ X19)
% 12.85/13.03          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.03          | ~ (v2_struct_0 @ X20)
% 12.85/13.03          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.03  thf('129', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ sk_B_1)
% 12.85/13.03         | ~ (v4_orders_2 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('sup-', [status(thm)], ['127', '128'])).
% 12.85/13.03  thf('130', plain,
% 12.85/13.03      (((l1_waybel_0 @ sk_B_1 @ sk_A)) <= (((l1_waybel_0 @ sk_B_1 @ sk_A)))),
% 12.85/13.03      inference('split', [status(esa)], ['4'])).
% 12.85/13.03  thf('131', plain, (((v7_waybel_0 @ sk_B_1)) <= (((v7_waybel_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['6'])).
% 12.85/13.03  thf('132', plain, (((v4_orders_2 @ sk_B_1)) <= (((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['8'])).
% 12.85/13.03  thf('133', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.03      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.03  thf('134', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 12.85/13.03  thf('135', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_B_1)))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('simplify', [status(thm)], ['134'])).
% 12.85/13.03  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('137', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_B_1)
% 12.85/13.03         | ~ (v2_struct_0 @ (sk_D_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1 @ sk_A))))
% 12.85/13.03         <= (((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['135', '136'])).
% 12.85/13.03  thf('138', plain,
% 12.85/13.03      (((v2_struct_0 @ sk_B_1))
% 12.85/13.03         <= ((![X38 : $i]:
% 12.85/13.03                (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1)
% 12.85/13.03                 | ~ (v3_yellow_6 @ X38 @ sk_A))) & 
% 12.85/13.03             ((v1_compts_1 @ sk_A)) & 
% 12.85/13.03             ((l1_waybel_0 @ sk_B_1 @ sk_A)) & 
% 12.85/13.03             ((v7_waybel_0 @ sk_B_1)) & 
% 12.85/13.03             ((v4_orders_2 @ sk_B_1)))),
% 12.85/13.03      inference('clc', [status(thm)], ['126', '137'])).
% 12.85/13.03  thf('139', plain,
% 12.85/13.03      ((~ (v2_struct_0 @ sk_B_1)) <= (~ ((v2_struct_0 @ sk_B_1)))),
% 12.85/13.03      inference('split', [status(esa)], ['10'])).
% 12.85/13.03  thf('140', plain,
% 12.85/13.03      (~ ((l1_waybel_0 @ sk_B_1 @ sk_A)) | ~ ((v1_compts_1 @ sk_A)) | 
% 12.85/13.03       ~
% 12.85/13.03       (![X38 : $i]:
% 12.85/13.03          (~ (m2_yellow_6 @ X38 @ sk_A @ sk_B_1) | ~ (v3_yellow_6 @ X38 @ sk_A))) | 
% 12.85/13.03       ~ ((v7_waybel_0 @ sk_B_1)) | ~ ((v4_orders_2 @ sk_B_1)) | 
% 12.85/13.03       ((v2_struct_0 @ sk_B_1))),
% 12.85/13.03      inference('sup-', [status(thm)], ['138', '139'])).
% 12.85/13.03  thf('141', plain,
% 12.85/13.03      ((![X39 : $i]:
% 12.85/13.03          ((v2_struct_0 @ X39)
% 12.85/13.03           | ~ (v4_orders_2 @ X39)
% 12.85/13.03           | ~ (v7_waybel_0 @ X39)
% 12.85/13.03           | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03           | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) | 
% 12.85/13.03       ((v1_compts_1 @ sk_A))),
% 12.85/13.03      inference('split', [status(esa)], ['13'])).
% 12.85/13.03  thf(t36_yellow19, axiom,
% 12.85/13.03    (![A:$i]:
% 12.85/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.85/13.03       ( ( v1_compts_1 @ A ) <=>
% 12.85/13.03         ( ![B:$i]:
% 12.85/13.03           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.85/13.03               ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.03             ( ~( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) ) & 
% 12.85/13.03                  ( ![C:$i]:
% 12.85/13.03                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.85/13.03                      ( ~( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ) ) ) ))).
% 12.85/13.03  thf('142', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v7_waybel_0 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('143', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v4_orders_2 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('144', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v7_waybel_0 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('145', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v4_orders_2 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('146', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((l1_waybel_0 @ (sk_B @ X35) @ X35)
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('147', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v4_orders_2 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('148', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v7_waybel_0 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('149', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((l1_waybel_0 @ (sk_B @ X35) @ X35)
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('150', plain,
% 12.85/13.03      ((![X39 : $i]:
% 12.85/13.03          ((v2_struct_0 @ X39)
% 12.85/13.03           | ~ (v4_orders_2 @ X39)
% 12.85/13.03           | ~ (v7_waybel_0 @ X39)
% 12.85/13.03           | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03           | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('split', [status(esa)], ['0'])).
% 12.85/13.03  thf('151', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['149', '150'])).
% 12.85/13.03  thf('152', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('154', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['151', '152', '153'])).
% 12.85/13.03  thf('155', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['148', '154'])).
% 12.85/13.03  thf('156', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('157', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('158', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['155', '156', '157'])).
% 12.85/13.03  thf('159', plain,
% 12.85/13.03      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['158'])).
% 12.85/13.03  thf('160', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['147', '159'])).
% 12.85/13.03  thf('161', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('162', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('163', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['160', '161', '162'])).
% 12.85/13.03  thf('164', plain,
% 12.85/13.03      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['163'])).
% 12.85/13.03  thf('165', plain,
% 12.85/13.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.03         (~ (l1_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X19)
% 12.85/13.03          | ~ (v4_orders_2 @ X19)
% 12.85/13.03          | ~ (v7_waybel_0 @ X19)
% 12.85/13.03          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.03          | (v7_waybel_0 @ X20)
% 12.85/13.03          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.03  thf('166', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['164', '165'])).
% 12.85/13.03  thf('167', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.03      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.03  thf('168', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['166', '167'])).
% 12.85/13.03  thf('169', plain,
% 12.85/13.03      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['168'])).
% 12.85/13.03  thf('170', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['146', '169'])).
% 12.85/13.03  thf('171', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('173', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['170', '171', '172'])).
% 12.85/13.03  thf('174', plain,
% 12.85/13.03      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['173'])).
% 12.85/13.03  thf('175', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['145', '174'])).
% 12.85/13.03  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('178', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['175', '176', '177'])).
% 12.85/13.03  thf('179', plain,
% 12.85/13.03      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['178'])).
% 12.85/13.03  thf('180', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['144', '179'])).
% 12.85/13.03  thf('181', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('182', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('183', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['180', '181', '182'])).
% 12.85/13.03  thf('184', plain,
% 12.85/13.03      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['183'])).
% 12.85/13.03  thf('185', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v4_orders_2 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('186', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v7_waybel_0 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('187', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((l1_waybel_0 @ (sk_B @ X35) @ X35)
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('188', plain,
% 12.85/13.03      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['163'])).
% 12.85/13.03  thf('189', plain,
% 12.85/13.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.03         (~ (l1_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X19)
% 12.85/13.03          | ~ (v4_orders_2 @ X19)
% 12.85/13.03          | ~ (v7_waybel_0 @ X19)
% 12.85/13.03          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.03          | (v4_orders_2 @ X20)
% 12.85/13.03          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.03  thf('190', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['188', '189'])).
% 12.85/13.03  thf('191', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.03      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.03  thf('192', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['190', '191'])).
% 12.85/13.03  thf('193', plain,
% 12.85/13.03      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['192'])).
% 12.85/13.03  thf('194', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['187', '193'])).
% 12.85/13.03  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('197', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['194', '195', '196'])).
% 12.85/13.03  thf('198', plain,
% 12.85/13.03      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['197'])).
% 12.85/13.03  thf('199', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['186', '198'])).
% 12.85/13.03  thf('200', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('201', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('202', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['199', '200', '201'])).
% 12.85/13.03  thf('203', plain,
% 12.85/13.03      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['202'])).
% 12.85/13.03  thf('204', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['185', '203'])).
% 12.85/13.03  thf('205', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('206', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('207', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['204', '205', '206'])).
% 12.85/13.03  thf('208', plain,
% 12.85/13.03      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['207'])).
% 12.85/13.03  thf('209', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v4_orders_2 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('210', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v7_waybel_0 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('211', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((l1_waybel_0 @ (sk_B @ X35) @ X35)
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('212', plain,
% 12.85/13.03      ((![X39 : $i]:
% 12.85/13.03          ((v2_struct_0 @ X39)
% 12.85/13.03           | ~ (v4_orders_2 @ X39)
% 12.85/13.03           | ~ (v7_waybel_0 @ X39)
% 12.85/13.03           | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03           | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('split', [status(esa)], ['13'])).
% 12.85/13.03  thf('213', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['211', '212'])).
% 12.85/13.03  thf('214', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('215', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('216', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('demod', [status(thm)], ['213', '214', '215'])).
% 12.85/13.03  thf('217', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['210', '216'])).
% 12.85/13.03  thf('218', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('220', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('demod', [status(thm)], ['217', '218', '219'])).
% 12.85/13.03  thf('221', plain,
% 12.85/13.03      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['220'])).
% 12.85/13.03  thf('222', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['209', '221'])).
% 12.85/13.03  thf('223', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('225', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('demod', [status(thm)], ['222', '223', '224'])).
% 12.85/13.03  thf('226', plain,
% 12.85/13.03      ((((v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['225'])).
% 12.85/13.03  thf('227', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v7_waybel_0 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('228', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v4_orders_2 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('229', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((l1_waybel_0 @ (sk_B @ X35) @ X35)
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('230', plain,
% 12.85/13.03      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['163'])).
% 12.85/13.03  thf('231', plain,
% 12.85/13.03      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.03         (~ (l1_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X18)
% 12.85/13.03          | (v2_struct_0 @ X19)
% 12.85/13.03          | ~ (v4_orders_2 @ X19)
% 12.85/13.03          | ~ (v7_waybel_0 @ X19)
% 12.85/13.03          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.03          | (l1_waybel_0 @ X20 @ X18)
% 12.85/13.03          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.03  thf('232', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['230', '231'])).
% 12.85/13.03  thf('233', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.03      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.03  thf('234', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['232', '233'])).
% 12.85/13.03  thf('235', plain,
% 12.85/13.03      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['234'])).
% 12.85/13.03  thf('236', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['229', '235'])).
% 12.85/13.03  thf('237', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('238', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('239', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['236', '237', '238'])).
% 12.85/13.03  thf('240', plain,
% 12.85/13.03      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['239'])).
% 12.85/13.03  thf('241', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['228', '240'])).
% 12.85/13.03  thf('242', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('243', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('244', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['241', '242', '243'])).
% 12.85/13.03  thf('245', plain,
% 12.85/13.03      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['244'])).
% 12.85/13.03  thf('246', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['227', '245'])).
% 12.85/13.03  thf('247', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('248', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('249', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['246', '247', '248'])).
% 12.85/13.03  thf('250', plain,
% 12.85/13.03      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['249'])).
% 12.85/13.03  thf('251', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v7_waybel_0 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('252', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((v4_orders_2 @ (sk_B @ X35))
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('253', plain,
% 12.85/13.03      (![X35 : $i]:
% 12.85/13.03         ((l1_waybel_0 @ (sk_B @ X35) @ X35)
% 12.85/13.03          | (v1_compts_1 @ X35)
% 12.85/13.03          | ~ (l1_pre_topc @ X35)
% 12.85/13.03          | ~ (v2_pre_topc @ X35)
% 12.85/13.03          | (v2_struct_0 @ X35))),
% 12.85/13.03      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.03  thf('254', plain,
% 12.85/13.03      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['163'])).
% 12.85/13.03  thf('255', plain,
% 12.85/13.03      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['183'])).
% 12.85/13.03  thf('256', plain,
% 12.85/13.03      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['207'])).
% 12.85/13.03  thf('257', plain,
% 12.85/13.03      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['249'])).
% 12.85/13.03  thf('258', plain,
% 12.85/13.03      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['207'])).
% 12.85/13.03  thf('259', plain,
% 12.85/13.03      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['183'])).
% 12.85/13.03  thf('260', plain,
% 12.85/13.03      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['249'])).
% 12.85/13.03  thf('261', plain,
% 12.85/13.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 12.85/13.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.85/13.03  thf(d18_yellow_6, axiom,
% 12.85/13.03    (![A:$i]:
% 12.85/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.85/13.03       ( ![B:$i]:
% 12.85/13.03         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.85/13.03             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.03           ( ![C:$i]:
% 12.85/13.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.85/13.03               ( ( ( C ) = ( k10_yellow_6 @ A @ B ) ) <=>
% 12.85/13.03                 ( ![D:$i]:
% 12.85/13.03                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 12.85/13.03                     ( ( r2_hidden @ D @ C ) <=>
% 12.85/13.03                       ( ![E:$i]:
% 12.85/13.03                         ( ( m1_connsp_2 @ E @ A @ D ) =>
% 12.85/13.03                           ( r1_waybel_0 @ A @ B @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 12.85/13.03  thf('262', plain,
% 12.85/13.03      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X10)
% 12.85/13.03          | ~ (v4_orders_2 @ X10)
% 12.85/13.03          | ~ (v7_waybel_0 @ X10)
% 12.85/13.03          | ~ (l1_waybel_0 @ X10 @ X11)
% 12.85/13.03          | (m1_subset_1 @ (sk_D @ X12 @ X10 @ X11) @ (u1_struct_0 @ X11))
% 12.85/13.03          | ((X12) = (k10_yellow_6 @ X11 @ X10))
% 12.85/13.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 12.85/13.03          | ~ (l1_pre_topc @ X11)
% 12.85/13.03          | ~ (v2_pre_topc @ X11)
% 12.85/13.03          | (v2_struct_0 @ X11))),
% 12.85/13.03      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.85/13.03  thf('263', plain,
% 12.85/13.03      (![X0 : $i, X1 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X0)
% 12.85/13.03          | ~ (v2_pre_topc @ X0)
% 12.85/13.03          | ~ (l1_pre_topc @ X0)
% 12.85/13.03          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 12.85/13.03          | (m1_subset_1 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ (u1_struct_0 @ X0))
% 12.85/13.03          | ~ (l1_waybel_0 @ X1 @ X0)
% 12.85/13.03          | ~ (v7_waybel_0 @ X1)
% 12.85/13.03          | ~ (v4_orders_2 @ X1)
% 12.85/13.03          | (v2_struct_0 @ X1))),
% 12.85/13.03      inference('sup-', [status(thm)], ['261', '262'])).
% 12.85/13.03  thf('264', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['260', '263'])).
% 12.85/13.03  thf('265', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('266', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('267', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['264', '265', '266'])).
% 12.85/13.03  thf('268', plain,
% 12.85/13.03      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['267'])).
% 12.85/13.03  thf('269', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['259', '268'])).
% 12.85/13.03  thf('270', plain,
% 12.85/13.03      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['269'])).
% 12.85/13.03  thf('271', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['258', '270'])).
% 12.85/13.03  thf('272', plain,
% 12.85/13.03      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['271'])).
% 12.85/13.03  thf('273', plain,
% 12.85/13.03      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['271'])).
% 12.85/13.03  thf('274', plain,
% 12.85/13.03      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['207'])).
% 12.85/13.03  thf('275', plain,
% 12.85/13.03      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['183'])).
% 12.85/13.03  thf('276', plain,
% 12.85/13.03      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['249'])).
% 12.85/13.03  thf('277', plain,
% 12.85/13.03      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (m1_subset_1 @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (u1_struct_0 @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['271'])).
% 12.85/13.03  thf('278', plain,
% 12.85/13.03      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['207'])).
% 12.85/13.03  thf('279', plain,
% 12.85/13.03      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['183'])).
% 12.85/13.03  thf('280', plain,
% 12.85/13.03      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['249'])).
% 12.85/13.03  thf('281', plain,
% 12.85/13.03      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['183'])).
% 12.85/13.03  thf('282', plain,
% 12.85/13.03      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['207'])).
% 12.85/13.03  thf('283', plain,
% 12.85/13.03      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['249'])).
% 12.85/13.03  thf(dt_k10_yellow_6, axiom,
% 12.85/13.03    (![A:$i,B:$i]:
% 12.85/13.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 12.85/13.03         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 12.85/13.03         ( v4_orders_2 @ B ) & ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.03       ( m1_subset_1 @
% 12.85/13.03         ( k10_yellow_6 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 12.85/13.03  thf('284', plain,
% 12.85/13.03      (![X16 : $i, X17 : $i]:
% 12.85/13.03         (~ (l1_pre_topc @ X16)
% 12.85/13.03          | ~ (v2_pre_topc @ X16)
% 12.85/13.03          | (v2_struct_0 @ X16)
% 12.85/13.03          | (v2_struct_0 @ X17)
% 12.85/13.03          | ~ (v4_orders_2 @ X17)
% 12.85/13.03          | ~ (v7_waybel_0 @ X17)
% 12.85/13.03          | ~ (l1_waybel_0 @ X17 @ X16)
% 12.85/13.03          | (m1_subset_1 @ (k10_yellow_6 @ X16 @ X17) @ 
% 12.85/13.03             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 12.85/13.03      inference('cnf', [status(esa)], [dt_k10_yellow_6])).
% 12.85/13.03  thf('285', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.03            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03         | ~ (l1_pre_topc @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['283', '284'])).
% 12.85/13.03  thf('286', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('287', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('288', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.03            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['285', '286', '287'])).
% 12.85/13.03  thf('289', plain,
% 12.85/13.03      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.03            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['288'])).
% 12.85/13.03  thf('290', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.03            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['282', '289'])).
% 12.85/13.03  thf('291', plain,
% 12.85/13.03      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.03            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['290'])).
% 12.85/13.03  thf('292', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.03            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['281', '291'])).
% 12.85/13.03  thf('293', plain,
% 12.85/13.03      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.03            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['292'])).
% 12.85/13.03  thf('294', plain,
% 12.85/13.03      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X10)
% 12.85/13.03          | ~ (v4_orders_2 @ X10)
% 12.85/13.03          | ~ (v7_waybel_0 @ X10)
% 12.85/13.03          | ~ (l1_waybel_0 @ X10 @ X11)
% 12.85/13.03          | ((X12) != (k10_yellow_6 @ X11 @ X10))
% 12.85/13.03          | (r2_hidden @ X14 @ X12)
% 12.85/13.03          | (m1_connsp_2 @ (sk_E_1 @ X14 @ X10 @ X11) @ X11 @ X14)
% 12.85/13.03          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 12.85/13.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 12.85/13.03          | ~ (l1_pre_topc @ X11)
% 12.85/13.03          | ~ (v2_pre_topc @ X11)
% 12.85/13.03          | (v2_struct_0 @ X11))),
% 12.85/13.03      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.85/13.03  thf('295', plain,
% 12.85/13.03      (![X10 : $i, X11 : $i, X14 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X11)
% 12.85/13.03          | ~ (v2_pre_topc @ X11)
% 12.85/13.03          | ~ (l1_pre_topc @ X11)
% 12.85/13.03          | ~ (m1_subset_1 @ (k10_yellow_6 @ X11 @ X10) @ 
% 12.85/13.03               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 12.85/13.03          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 12.85/13.03          | (m1_connsp_2 @ (sk_E_1 @ X14 @ X10 @ X11) @ X11 @ X14)
% 12.85/13.03          | (r2_hidden @ X14 @ (k10_yellow_6 @ X11 @ X10))
% 12.85/13.03          | ~ (l1_waybel_0 @ X10 @ X11)
% 12.85/13.03          | ~ (v7_waybel_0 @ X10)
% 12.85/13.03          | ~ (v4_orders_2 @ X10)
% 12.85/13.03          | (v2_struct_0 @ X10))),
% 12.85/13.03      inference('simplify', [status(thm)], ['294'])).
% 12.85/13.03  thf('296', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.03           | ~ (l1_pre_topc @ sk_A)
% 12.85/13.03           | ~ (v2_pre_topc @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['293', '295'])).
% 12.85/13.03  thf('297', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('298', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.03  thf('299', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('demod', [status(thm)], ['296', '297', '298'])).
% 12.85/13.03  thf('300', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.03           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['299'])).
% 12.85/13.03  thf('301', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['280', '300'])).
% 12.85/13.03  thf('302', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['301'])).
% 12.85/13.03  thf('303', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['279', '302'])).
% 12.85/13.03  thf('304', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['303'])).
% 12.85/13.03  thf('305', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          ((v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ sk_A)
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['278', '304'])).
% 12.85/13.03  thf('306', plain,
% 12.85/13.03      ((![X0 : $i]:
% 12.85/13.03          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.03           | (m1_connsp_2 @ (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03              sk_A @ X0)
% 12.85/13.03           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03           | (v1_compts_1 @ sk_A)
% 12.85/13.03           | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['305'])).
% 12.85/13.03  thf('307', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (r2_hidden @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (m1_connsp_2 @ 
% 12.85/13.03            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('sup-', [status(thm)], ['277', '306'])).
% 12.85/13.03  thf('308', plain,
% 12.85/13.03      ((((m1_connsp_2 @ 
% 12.85/13.03          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03          sk_A @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.03         | (r2_hidden @ 
% 12.85/13.03            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.03            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.03         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.03         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.03         | (v2_struct_0 @ sk_A)))
% 12.85/13.03         <= ((![X39 : $i]:
% 12.85/13.03                ((v2_struct_0 @ X39)
% 12.85/13.03                 | ~ (v4_orders_2 @ X39)
% 12.85/13.03                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.03                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.03                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.03      inference('simplify', [status(thm)], ['307'])).
% 12.85/13.03  thf('309', plain,
% 12.85/13.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 12.85/13.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.85/13.03  thf('310', plain,
% 12.85/13.03      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X10)
% 12.85/13.03          | ~ (v4_orders_2 @ X10)
% 12.85/13.03          | ~ (v7_waybel_0 @ X10)
% 12.85/13.03          | ~ (l1_waybel_0 @ X10 @ X11)
% 12.85/13.03          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X12)
% 12.85/13.03          | (r1_waybel_0 @ X11 @ X10 @ X13)
% 12.85/13.03          | ~ (m1_connsp_2 @ X13 @ X11 @ (sk_D @ X12 @ X10 @ X11))
% 12.85/13.03          | ((X12) = (k10_yellow_6 @ X11 @ X10))
% 12.85/13.03          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 12.85/13.03          | ~ (l1_pre_topc @ X11)
% 12.85/13.03          | ~ (v2_pre_topc @ X11)
% 12.85/13.03          | (v2_struct_0 @ X11))),
% 12.85/13.03      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.85/13.03  thf('311', plain,
% 12.85/13.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.85/13.03         ((v2_struct_0 @ X0)
% 12.85/13.03          | ~ (v2_pre_topc @ X0)
% 12.85/13.03          | ~ (l1_pre_topc @ X0)
% 12.85/13.03          | ((k1_xboole_0) = (k10_yellow_6 @ X0 @ X1))
% 12.85/13.03          | ~ (m1_connsp_2 @ X2 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0))
% 12.85/13.03          | (r1_waybel_0 @ X0 @ X1 @ X2)
% 12.85/13.03          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 12.85/13.03          | ~ (l1_waybel_0 @ X1 @ X0)
% 12.85/13.03          | ~ (v7_waybel_0 @ X1)
% 12.85/13.03          | ~ (v4_orders_2 @ X1)
% 12.85/13.03          | (v2_struct_0 @ X1))),
% 12.85/13.03      inference('sup-', [status(thm)], ['309', '310'])).
% 12.85/13.03  thf('312', plain,
% 12.85/13.03      ((((v2_struct_0 @ sk_A)
% 12.85/13.03         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['308', '311'])).
% 12.85/13.04  thf('313', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('314', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('315', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['312', '313', '314'])).
% 12.85/13.04  thf('316', plain,
% 12.85/13.04      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['315'])).
% 12.85/13.04  thf('317', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['276', '316'])).
% 12.85/13.04  thf('318', plain,
% 12.85/13.04      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['317'])).
% 12.85/13.04  thf('319', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['275', '318'])).
% 12.85/13.04  thf('320', plain,
% 12.85/13.04      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['319'])).
% 12.85/13.04  thf('321', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04             (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['274', '320'])).
% 12.85/13.04  thf('322', plain,
% 12.85/13.04      ((((r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04          (sk_E_1 @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04           (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['321'])).
% 12.85/13.04  thf('323', plain,
% 12.85/13.04      ((((v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['207'])).
% 12.85/13.04  thf('324', plain,
% 12.85/13.04      ((((v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['183'])).
% 12.85/13.04  thf('325', plain,
% 12.85/13.04      ((((l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['249'])).
% 12.85/13.04  thf('326', plain,
% 12.85/13.04      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (m1_subset_1 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))) @ 
% 12.85/13.04            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['292'])).
% 12.85/13.04  thf('327', plain,
% 12.85/13.04      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 12.85/13.04         ((v2_struct_0 @ X10)
% 12.85/13.04          | ~ (v4_orders_2 @ X10)
% 12.85/13.04          | ~ (v7_waybel_0 @ X10)
% 12.85/13.04          | ~ (l1_waybel_0 @ X10 @ X11)
% 12.85/13.04          | ((X12) != (k10_yellow_6 @ X11 @ X10))
% 12.85/13.04          | (r2_hidden @ X14 @ X12)
% 12.85/13.04          | ~ (r1_waybel_0 @ X11 @ X10 @ (sk_E_1 @ X14 @ X10 @ X11))
% 12.85/13.04          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 12.85/13.04          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 12.85/13.04          | ~ (l1_pre_topc @ X11)
% 12.85/13.04          | ~ (v2_pre_topc @ X11)
% 12.85/13.04          | (v2_struct_0 @ X11))),
% 12.85/13.04      inference('cnf', [status(esa)], [d18_yellow_6])).
% 12.85/13.04  thf('328', plain,
% 12.85/13.04      (![X10 : $i, X11 : $i, X14 : $i]:
% 12.85/13.04         ((v2_struct_0 @ X11)
% 12.85/13.04          | ~ (v2_pre_topc @ X11)
% 12.85/13.04          | ~ (l1_pre_topc @ X11)
% 12.85/13.04          | ~ (m1_subset_1 @ (k10_yellow_6 @ X11 @ X10) @ 
% 12.85/13.04               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 12.85/13.04          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X11))
% 12.85/13.04          | ~ (r1_waybel_0 @ X11 @ X10 @ (sk_E_1 @ X14 @ X10 @ X11))
% 12.85/13.04          | (r2_hidden @ X14 @ (k10_yellow_6 @ X11 @ X10))
% 12.85/13.04          | ~ (l1_waybel_0 @ X10 @ X11)
% 12.85/13.04          | ~ (v7_waybel_0 @ X10)
% 12.85/13.04          | ~ (v4_orders_2 @ X10)
% 12.85/13.04          | (v2_struct_0 @ X10))),
% 12.85/13.04      inference('simplify', [status(thm)], ['327'])).
% 12.85/13.04  thf('329', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.04           | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04           | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['326', '328'])).
% 12.85/13.04  thf('330', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('331', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('332', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['329', '330', '331'])).
% 12.85/13.04  thf('333', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['332'])).
% 12.85/13.04  thf('334', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['325', '333'])).
% 12.85/13.04  thf('335', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['334'])).
% 12.85/13.04  thf('336', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['324', '335'])).
% 12.85/13.04  thf('337', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['336'])).
% 12.85/13.04  thf('338', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['323', '337'])).
% 12.85/13.04  thf('339', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 12.85/13.04           | ~ (r1_waybel_0 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04                (sk_E_1 @ X0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | (r2_hidden @ X0 @ (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['338'])).
% 12.85/13.04  thf('340', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ~ (m1_subset_1 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04              (u1_struct_0 @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['322', '339'])).
% 12.85/13.04  thf('341', plain,
% 12.85/13.04      (((~ (m1_subset_1 @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (u1_struct_0 @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['340'])).
% 12.85/13.04  thf('342', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['273', '341'])).
% 12.85/13.04  thf('343', plain,
% 12.85/13.04      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04          k1_xboole_0)
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['342'])).
% 12.85/13.04  thf(t29_waybel_9, axiom,
% 12.85/13.04    (![A:$i]:
% 12.85/13.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.85/13.04       ( ![B:$i]:
% 12.85/13.04         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.85/13.04             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.04           ( ![C:$i]:
% 12.85/13.04             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.85/13.04               ( ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) =>
% 12.85/13.04                 ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 12.85/13.04  thf('344', plain,
% 12.85/13.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 12.85/13.04         ((v2_struct_0 @ X23)
% 12.85/13.04          | ~ (v4_orders_2 @ X23)
% 12.85/13.04          | ~ (v7_waybel_0 @ X23)
% 12.85/13.04          | ~ (l1_waybel_0 @ X23 @ X24)
% 12.85/13.04          | ~ (r2_hidden @ X25 @ (k10_yellow_6 @ X24 @ X23))
% 12.85/13.04          | (r3_waybel_9 @ X24 @ X23 @ X25)
% 12.85/13.04          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 12.85/13.04          | ~ (l1_pre_topc @ X24)
% 12.85/13.04          | ~ (v2_pre_topc @ X24)
% 12.85/13.04          | (v2_struct_0 @ X24))),
% 12.85/13.04      inference('cnf', [status(esa)], [t29_waybel_9])).
% 12.85/13.04  thf('345', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | ~ (m1_subset_1 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04              (u1_struct_0 @ sk_A))
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['343', '344'])).
% 12.85/13.04  thf('346', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('347', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('348', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (m1_subset_1 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04              (u1_struct_0 @ sk_A))
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['345', '346', '347'])).
% 12.85/13.04  thf('349', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (m1_subset_1 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04              (u1_struct_0 @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['348'])).
% 12.85/13.04  thf('350', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['272', '349'])).
% 12.85/13.04  thf('351', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['350'])).
% 12.85/13.04  thf('352', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['257', '351'])).
% 12.85/13.04  thf('353', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['352'])).
% 12.85/13.04  thf('354', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['256', '353'])).
% 12.85/13.04  thf('355', plain,
% 12.85/13.04      (((~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['354'])).
% 12.85/13.04  thf('356', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['255', '355'])).
% 12.85/13.04  thf('357', plain,
% 12.85/13.04      ((((r3_waybel_9 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A)) @ 
% 12.85/13.04          (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['356'])).
% 12.85/13.04  thf('358', plain,
% 12.85/13.04      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (m1_subset_1 @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (u1_struct_0 @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['271'])).
% 12.85/13.04  thf(t31_waybel_9, axiom,
% 12.85/13.04    (![A:$i]:
% 12.85/13.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.85/13.04       ( ![B:$i]:
% 12.85/13.04         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 12.85/13.04             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 12.85/13.04           ( ![C:$i]:
% 12.85/13.04             ( ( m2_yellow_6 @ C @ A @ B ) =>
% 12.85/13.04               ( ![D:$i]:
% 12.85/13.04                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 12.85/13.04                   ( ( r3_waybel_9 @ A @ C @ D ) => ( r3_waybel_9 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 12.85/13.04  thf('359', plain,
% 12.85/13.04      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 12.85/13.04         ((v2_struct_0 @ X26)
% 12.85/13.04          | ~ (v4_orders_2 @ X26)
% 12.85/13.04          | ~ (v7_waybel_0 @ X26)
% 12.85/13.04          | ~ (l1_waybel_0 @ X26 @ X27)
% 12.85/13.04          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 12.85/13.04          | (r3_waybel_9 @ X27 @ X26 @ X28)
% 12.85/13.04          | ~ (r3_waybel_9 @ X27 @ X29 @ X28)
% 12.85/13.04          | ~ (m2_yellow_6 @ X29 @ X27 @ X26)
% 12.85/13.04          | ~ (l1_pre_topc @ X27)
% 12.85/13.04          | ~ (v2_pre_topc @ X27)
% 12.85/13.04          | (v2_struct_0 @ X27))),
% 12.85/13.04      inference('cnf', [status(esa)], [t31_waybel_9])).
% 12.85/13.04  thf('360', plain,
% 12.85/13.04      ((![X0 : $i, X1 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | (v2_struct_0 @ sk_A)
% 12.85/13.04           | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04           | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 12.85/13.04           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 12.85/13.04                (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.04           | ~ (v7_waybel_0 @ X0)
% 12.85/13.04           | ~ (v4_orders_2 @ X0)
% 12.85/13.04           | (v2_struct_0 @ X0)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['358', '359'])).
% 12.85/13.04  thf('361', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('362', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('363', plain,
% 12.85/13.04      ((![X0 : $i, X1 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | (v2_struct_0 @ sk_A)
% 12.85/13.04           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 12.85/13.04           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 12.85/13.04                (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.04           | ~ (v7_waybel_0 @ X0)
% 12.85/13.04           | ~ (v4_orders_2 @ X0)
% 12.85/13.04           | (v2_struct_0 @ X0)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['360', '361', '362'])).
% 12.85/13.04  thf('364', plain,
% 12.85/13.04      ((![X0 : $i, X1 : $i]:
% 12.85/13.04          ((v2_struct_0 @ X0)
% 12.85/13.04           | ~ (v4_orders_2 @ X0)
% 12.85/13.04           | ~ (v7_waybel_0 @ X0)
% 12.85/13.04           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.04           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (r3_waybel_9 @ sk_A @ X1 @ 
% 12.85/13.04                (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (m2_yellow_6 @ X1 @ sk_A @ X0)
% 12.85/13.04           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['363'])).
% 12.85/13.04  thf('365', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          ((v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | (r2_hidden @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04              k1_xboole_0)
% 12.85/13.04           | (v2_struct_0 @ sk_A)
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 12.85/13.04           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.04           | ~ (v7_waybel_0 @ X0)
% 12.85/13.04           | ~ (v4_orders_2 @ X0)
% 12.85/13.04           | (v2_struct_0 @ X0)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['357', '364'])).
% 12.85/13.04  thf('366', plain,
% 12.85/13.04      ((![X0 : $i]:
% 12.85/13.04          ((v2_struct_0 @ X0)
% 12.85/13.04           | ~ (v4_orders_2 @ X0)
% 12.85/13.04           | ~ (v7_waybel_0 @ X0)
% 12.85/13.04           | ~ (l1_waybel_0 @ X0 @ sk_A)
% 12.85/13.04           | (r3_waybel_9 @ sk_A @ X0 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04           | ~ (m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ X0)
% 12.85/13.04           | (r2_hidden @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04              k1_xboole_0)
% 12.85/13.04           | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04           | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04           | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04           | (v1_compts_1 @ sk_A)
% 12.85/13.04           | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['365'])).
% 12.85/13.04  thf('367', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['254', '366'])).
% 12.85/13.04  thf('368', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['367'])).
% 12.85/13.04  thf('369', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['253', '368'])).
% 12.85/13.04  thf('370', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('371', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('372', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['369', '370', '371'])).
% 12.85/13.04  thf('373', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['372'])).
% 12.85/13.04  thf('374', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['252', '373'])).
% 12.85/13.04  thf('375', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('376', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('377', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['374', '375', '376'])).
% 12.85/13.04  thf('378', plain,
% 12.85/13.04      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['377'])).
% 12.85/13.04  thf('379', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['251', '378'])).
% 12.85/13.04  thf('380', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('381', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('382', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['379', '380', '381'])).
% 12.85/13.04  thf('383', plain,
% 12.85/13.04      ((((r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04          (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['382'])).
% 12.85/13.04  thf('384', plain,
% 12.85/13.04      (((((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (m1_subset_1 @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            (u1_struct_0 @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['271'])).
% 12.85/13.04  thf('385', plain,
% 12.85/13.04      (![X35 : $i, X36 : $i]:
% 12.85/13.04         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X35))
% 12.85/13.04          | ~ (r3_waybel_9 @ X35 @ (sk_B @ X35) @ X36)
% 12.85/13.04          | (v1_compts_1 @ X35)
% 12.85/13.04          | ~ (l1_pre_topc @ X35)
% 12.85/13.04          | ~ (v2_pre_topc @ X35)
% 12.85/13.04          | (v2_struct_0 @ X35))),
% 12.85/13.04      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.04  thf('386', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['384', '385'])).
% 12.85/13.04  thf('387', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('388', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('389', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | ~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['386', '387', '388'])).
% 12.85/13.04  thf('390', plain,
% 12.85/13.04      (((~ (r3_waybel_9 @ sk_A @ (sk_B @ sk_A) @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['389'])).
% 12.85/13.04  thf('391', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (r2_hidden @ 
% 12.85/13.04            (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04            k1_xboole_0)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['383', '390'])).
% 12.85/13.04  thf('392', plain,
% 12.85/13.04      ((((r2_hidden @ (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A) @ 
% 12.85/13.04          k1_xboole_0)
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['391'])).
% 12.85/13.04  thf('393', plain,
% 12.85/13.04      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 12.85/13.04      inference('cnf', [status(esa)], [t7_ordinal1])).
% 12.85/13.04  thf('394', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))
% 12.85/13.04         | ~ (r1_tarski @ k1_xboole_0 @ 
% 12.85/13.04              (sk_D @ k1_xboole_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['392', '393'])).
% 12.85/13.04  thf('395', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 12.85/13.04      inference('sup-', [status(thm)], ['115', '116'])).
% 12.85/13.04  thf('396', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ((k1_xboole_0) = (k10_yellow_6 @ sk_A @ (sk_C_2 @ (sk_B @ sk_A))))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['394', '395'])).
% 12.85/13.04  thf('397', plain,
% 12.85/13.04      (![X21 : $i, X22 : $i]:
% 12.85/13.04         ((v2_struct_0 @ X21)
% 12.85/13.04          | ~ (v4_orders_2 @ X21)
% 12.85/13.04          | ~ (v7_waybel_0 @ X21)
% 12.85/13.04          | ~ (l1_waybel_0 @ X21 @ X22)
% 12.85/13.04          | ~ (v3_yellow_6 @ X21 @ X22)
% 12.85/13.04          | ((k10_yellow_6 @ X22 @ X21) != (k1_xboole_0))
% 12.85/13.04          | ~ (l1_pre_topc @ X22)
% 12.85/13.04          | ~ (v2_pre_topc @ X22)
% 12.85/13.04          | (v2_struct_0 @ X22))),
% 12.85/13.04      inference('cnf', [status(esa)], [d19_yellow_6])).
% 12.85/13.04  thf('398', plain,
% 12.85/13.04      (((((k1_xboole_0) != (k1_xboole_0))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['396', '397'])).
% 12.85/13.04  thf('399', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('400', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('401', plain,
% 12.85/13.04      (((((k1_xboole_0) != (k1_xboole_0))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['398', '399', '400'])).
% 12.85/13.04  thf('402', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['401'])).
% 12.85/13.04  thf('403', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['250', '402'])).
% 12.85/13.04  thf('404', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v3_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['403'])).
% 12.85/13.04  thf('405', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['226', '404'])).
% 12.85/13.04  thf('406', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['405'])).
% 12.85/13.04  thf('407', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['208', '406'])).
% 12.85/13.04  thf('408', plain,
% 12.85/13.04      (((~ (v7_waybel_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['407'])).
% 12.85/13.04  thf('409', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['184', '408'])).
% 12.85/13.04  thf('410', plain,
% 12.85/13.04      ((((v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['409'])).
% 12.85/13.04  thf('411', plain,
% 12.85/13.04      (![X35 : $i]:
% 12.85/13.04         ((l1_waybel_0 @ (sk_B @ X35) @ X35)
% 12.85/13.04          | (v1_compts_1 @ X35)
% 12.85/13.04          | ~ (l1_pre_topc @ X35)
% 12.85/13.04          | ~ (v2_pre_topc @ X35)
% 12.85/13.04          | (v2_struct_0 @ X35))),
% 12.85/13.04      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.04  thf('412', plain,
% 12.85/13.04      ((((m2_yellow_6 @ (sk_C_2 @ (sk_B @ sk_A)) @ sk_A @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['163'])).
% 12.85/13.04  thf('413', plain,
% 12.85/13.04      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.85/13.04         (~ (l1_struct_0 @ X18)
% 12.85/13.04          | (v2_struct_0 @ X18)
% 12.85/13.04          | (v2_struct_0 @ X19)
% 12.85/13.04          | ~ (v4_orders_2 @ X19)
% 12.85/13.04          | ~ (v7_waybel_0 @ X19)
% 12.85/13.04          | ~ (l1_waybel_0 @ X19 @ X18)
% 12.85/13.04          | ~ (v2_struct_0 @ X20)
% 12.85/13.04          | ~ (m2_yellow_6 @ X20 @ X18 @ X19))),
% 12.85/13.04      inference('cnf', [status(esa)], [dt_m2_yellow_6])).
% 12.85/13.04  thf('414', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (l1_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['412', '413'])).
% 12.85/13.04  thf('415', plain, ((l1_struct_0 @ sk_A)),
% 12.85/13.04      inference('sup-', [status(thm)], ['59', '60'])).
% 12.85/13.04  thf('416', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['414', '415'])).
% 12.85/13.04  thf('417', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (l1_waybel_0 @ (sk_B @ sk_A) @ sk_A)
% 12.85/13.04         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['416'])).
% 12.85/13.04  thf('418', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['411', '417'])).
% 12.85/13.04  thf('419', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('420', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('421', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['418', '419', '420'])).
% 12.85/13.04  thf('422', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v2_struct_0 @ (sk_C_2 @ (sk_B @ sk_A)))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['421'])).
% 12.85/13.04  thf('423', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v4_orders_2 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['410', '422'])).
% 12.85/13.04  thf('424', plain,
% 12.85/13.04      (((~ (v4_orders_2 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['423'])).
% 12.85/13.04  thf('425', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['143', '424'])).
% 12.85/13.04  thf('426', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('427', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('428', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | ~ (v7_waybel_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['425', '426', '427'])).
% 12.85/13.04  thf('429', plain,
% 12.85/13.04      (((~ (v7_waybel_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['428'])).
% 12.85/13.04  thf('430', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['142', '429'])).
% 12.85/13.04  thf('431', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('432', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('433', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['430', '431', '432'])).
% 12.85/13.04  thf('434', plain,
% 12.85/13.04      ((((v2_struct_0 @ (sk_B @ sk_A))
% 12.85/13.04         | (v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['433'])).
% 12.85/13.04  thf('435', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('436', plain,
% 12.85/13.04      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ (sk_B @ sk_A))))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('clc', [status(thm)], ['434', '435'])).
% 12.85/13.04  thf('437', plain,
% 12.85/13.04      (![X35 : $i]:
% 12.85/13.04         (~ (v2_struct_0 @ (sk_B @ X35))
% 12.85/13.04          | (v1_compts_1 @ X35)
% 12.85/13.04          | ~ (l1_pre_topc @ X35)
% 12.85/13.04          | ~ (v2_pre_topc @ X35)
% 12.85/13.04          | (v2_struct_0 @ X35))),
% 12.85/13.04      inference('cnf', [status(esa)], [t36_yellow19])).
% 12.85/13.04  thf('438', plain,
% 12.85/13.04      ((((v1_compts_1 @ sk_A)
% 12.85/13.04         | (v2_struct_0 @ sk_A)
% 12.85/13.04         | ~ (v2_pre_topc @ sk_A)
% 12.85/13.04         | ~ (l1_pre_topc @ sk_A)
% 12.85/13.04         | (v1_compts_1 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('sup-', [status(thm)], ['436', '437'])).
% 12.85/13.04  thf('439', plain, ((v2_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('440', plain, ((l1_pre_topc @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('441', plain,
% 12.85/13.04      ((((v1_compts_1 @ sk_A) | (v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('demod', [status(thm)], ['438', '439', '440'])).
% 12.85/13.04  thf('442', plain,
% 12.85/13.04      ((((v2_struct_0 @ sk_A) | (v1_compts_1 @ sk_A)))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('simplify', [status(thm)], ['441'])).
% 12.85/13.04  thf('443', plain, (~ (v2_struct_0 @ sk_A)),
% 12.85/13.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.85/13.04  thf('444', plain,
% 12.85/13.04      (((v1_compts_1 @ sk_A))
% 12.85/13.04         <= ((![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) & 
% 12.85/13.04             (![X39 : $i]:
% 12.85/13.04                ((v2_struct_0 @ X39)
% 12.85/13.04                 | ~ (v4_orders_2 @ X39)
% 12.85/13.04                 | ~ (v7_waybel_0 @ X39)
% 12.85/13.04                 | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04                 | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39))))),
% 12.85/13.04      inference('clc', [status(thm)], ['442', '443'])).
% 12.85/13.04  thf('445', plain, ((~ (v1_compts_1 @ sk_A)) <= (~ ((v1_compts_1 @ sk_A)))),
% 12.85/13.04      inference('split', [status(esa)], ['2'])).
% 12.85/13.04  thf('446', plain,
% 12.85/13.04      (~
% 12.85/13.04       (![X39 : $i]:
% 12.85/13.04          ((v2_struct_0 @ X39)
% 12.85/13.04           | ~ (v4_orders_2 @ X39)
% 12.85/13.04           | ~ (v7_waybel_0 @ X39)
% 12.85/13.04           | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04           | (v3_yellow_6 @ (sk_C_2 @ X39) @ sk_A))) | 
% 12.85/13.04       ((v1_compts_1 @ sk_A)) | 
% 12.85/13.04       ~
% 12.85/13.04       (![X39 : $i]:
% 12.85/13.04          ((v2_struct_0 @ X39)
% 12.85/13.04           | ~ (v4_orders_2 @ X39)
% 12.85/13.04           | ~ (v7_waybel_0 @ X39)
% 12.85/13.04           | ~ (l1_waybel_0 @ X39 @ sk_A)
% 12.85/13.04           | (m2_yellow_6 @ (sk_C_2 @ X39) @ sk_A @ X39)))),
% 12.85/13.04      inference('sup-', [status(thm)], ['444', '445'])).
% 12.85/13.04  thf('447', plain, ($false),
% 12.85/13.04      inference('sat_resolution*', [status(thm)],
% 12.85/13.04                ['1', '3', '5', '7', '9', '11', '140', '141', '446'])).
% 12.85/13.04  
% 12.85/13.04  % SZS output end Refutation
% 12.85/13.04  
% 12.85/13.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
