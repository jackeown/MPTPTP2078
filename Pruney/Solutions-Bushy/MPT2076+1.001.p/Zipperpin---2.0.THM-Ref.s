%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2076+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UMVt61tX6P

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 560 expanded)
%              Number of leaves         :   20 ( 147 expanded)
%              Depth                    :   37
%              Number of atoms          : 1565 (10277 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)

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

thf(t36_yellow19,conjecture,(
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
             => ~ ( ( r2_hidden @ B @ ( k6_yellow_6 @ A ) )
                  & ! [C: $i] :
                      ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                     => ~ ( r3_waybel_9 @ A @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_yellow19])).

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
      | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) )
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

thf('51',plain,(
    ! [X3: $i] :
      ( ( r2_hidden @ ( sk_B @ X3 ) @ ( k6_yellow_6 @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('52',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) )
   <= ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
        | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['52'])).

thf('55',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','10','45','54'])).

thf('56',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ X5 @ ( sk_C_1 @ X5 ) ) ) ),
    inference(simpl_trail,[status(thm)],['53','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( ( v4_orders_2 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('77',plain,(
    ! [X3: $i] :
      ( ( v7_waybel_0 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('78',plain,(
    ! [X3: $i] :
      ( ( l1_waybel_0 @ ( sk_B @ X3 ) @ X3 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( r2_hidden @ ( sk_B @ X3 ) @ ( k6_yellow_6 @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('80',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('81',plain,
    ( ! [X5: $i] :
        ( ( v2_struct_0 @ X5 )
        | ~ ( v4_orders_2 @ X5 )
        | ~ ( v7_waybel_0 @ X5 )
        | ~ ( l1_waybel_0 @ X5 @ sk_A )
        | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
        | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('82',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','4','6','8','10','45','81'])).

thf('83',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v7_waybel_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ sk_A )
      | ~ ( r2_hidden @ X5 @ ( k6_yellow_6 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X5 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_waybel_0 @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_waybel_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_orders_2 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ~ ( r3_waybel_9 @ X3 @ ( sk_B @ X3 ) @ X2 )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B @ sk_A ) @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ ( sk_B @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ~ ( v1_compts_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','46'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_struct_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X3: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X3 ) )
      | ( v1_compts_1 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l38_yellow19])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_compts_1 @ sk_A ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_compts_1 @ sk_A ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['47','121'])).


%------------------------------------------------------------------------------
