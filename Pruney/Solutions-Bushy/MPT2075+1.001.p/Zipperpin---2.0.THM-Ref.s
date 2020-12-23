%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2075+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j72uraLCsy

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:45 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 538 expanded)
%              Number of leaves         :   20 ( 141 expanded)
%              Depth                    :   32
%              Number of atoms          : 1351 (8877 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_yellow_6_type,type,(
    k6_yellow_6: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(t35_yellow19,conjecture,(
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
                  ( ( r3_waybel_9 @ A @ B @ C )
                  & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_yellow19])).

thf('0',plain,(
    ! [X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 )
      | ~ ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 ) )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( v4_orders_2 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v4_orders_2 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v1_compts_1 @ sk_A )
    | ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('12',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('15',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

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

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X0 )
      | ( r3_waybel_9 @ X0 @ X1 @ ( sk_C @ X1 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('17',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v4_orders_2 @ sk_B_1 )
   <= ( v4_orders_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('27',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('28',plain,
    ( ( v7_waybel_0 @ sk_B_1 )
   <= ( v7_waybel_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('29',plain,
    ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_compts_1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l37_yellow19])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v4_orders_2 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 ) )
   <= ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ! [X4: $i] :
          ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( ! [X4: $i] :
          ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B_1 )
   <= ( ! [X4: $i] :
          ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_1 @ sk_A )
      & ( v7_waybel_0 @ sk_B_1 )
      & ( v4_orders_2 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( v2_struct_0 @ sk_B_1 )
   <= ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('45',plain,
    ( ~ ( v1_compts_1 @ sk_A )
    | ~ ( v4_orders_2 @ sk_B_1 )
    | ~ ( v7_waybel_0 @ sk_B_1 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ~ ! [X4: $i] :
          ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r3_waybel_9 @ sk_A @ sk_B_1 @ X4 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_compts_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','10','45'])).

thf('47',plain,(
    ~ ( v1_compts_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf(l38_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ~ ( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) )
                & ! [C: $i] :
                    ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                   => ~ ( r3_waybel_9 @ A @ B @ C ) ) ) )
       => ( v1_compts_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X3: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('49',plain,(
    ! [X3: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X3 ) @ X3 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('51',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) )
   <= ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('52',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('53',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','10','45','52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) ) ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X3: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('71',plain,(
    ! [X3: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X3 ) @ X3 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B @ sk_A ) ) )
   <= ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['72'])).

thf('79',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','10','45','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r3_waybel_9 @ X3 @ ( sk_B @ X3 ) @ X2 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( v1_compts_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_struct_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X3: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_compts_1 @ sk_A ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['47','109'])).


%------------------------------------------------------------------------------
