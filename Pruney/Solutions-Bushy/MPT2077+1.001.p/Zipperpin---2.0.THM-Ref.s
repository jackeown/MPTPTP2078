%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2077+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7AGkVbKvZX

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:46 EST 2020

% Result     : Theorem 51.63s
% Output     : Refutation 51.63s
% Verified   : 
% Statistics : Number of formulae       :  436 (2360 expanded)
%              Number of leaves         :   42 ( 637 expanded)
%              Depth                    :   83
%              Number of atoms          : 8580 (47426 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m2_yellow_6_type,type,(
    m2_yellow_6: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r3_waybel_9_type,type,(
    r3_waybel_9: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X32: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X32: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v7_waybel_0 @ X32 )
      | ~ ( l1_waybel_0 @ X32 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 )
      | ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) )
    | ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

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

thf('4',plain,(
    ! [X21: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('5',plain,(
    ! [X21: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('6',plain,(
    ! [X21: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('7',plain,(
    ! [X21: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('8',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('9',plain,(
    ! [X21: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('10',plain,(
    ! [X21: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('11',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('12',plain,
    ( ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['25'])).

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

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( v7_waybel_0 @ X7 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['8','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['7','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['6','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X21: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('51',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('52',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( v4_orders_2 @ X7 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['50','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['49','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X21: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('74',plain,(
    ! [X21: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('75',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('76',plain,
    ( ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X21: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('92',plain,(
    ! [X21: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('93',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('94',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('95',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( l1_waybel_0 @ X7 @ X5 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['92','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['91','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X21: $i] :
      ( ( v7_waybel_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('116',plain,(
    ! [X21: $i] :
      ( ( v4_orders_2 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('117',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('118',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('119',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('120',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('121',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('122',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('123',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('126',plain,
    ( ( ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('127',plain,
    ( ( ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['113'])).

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

thf('128',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ~ ( v7_waybel_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X2 )
      | ( m1_subset_1 @ ( k10_yellow_6 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_yellow_6])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('138',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( m1_subset_1 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        | ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['124','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

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

thf('142',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v7_waybel_0 @ X9 )
      | ~ ( l1_waybel_0 @ X9 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k10_yellow_6 @ X10 @ X9 ) )
      | ( r3_waybel_9 @ X10 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_waybel_9])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_yellow_6 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k10_yellow_6 @ X1 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ( r3_waybel_9 @ X1 @ X0 @ ( sk_B @ ( k10_yellow_6 @ X1 @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['121','148'])).

thf('150',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['120','150'])).

thf('152',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['119','152'])).

thf('154',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['124','139'])).

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

thf('156',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r3_waybel_9 @ X15 @ X14 @ X16 )
      | ~ ( r3_waybel_9 @ X15 @ X17 @ X16 )
      | ~ ( m2_yellow_6 @ X17 @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_waybel_9])).

thf('157',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ~ ( r3_waybel_9 @ sk_A @ X1 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ~ ( m2_yellow_6 @ X1 @ sk_A @ X0 )
        | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
        | ~ ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ X0 )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['154','161'])).

thf('163',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ( r3_waybel_9 @ sk_A @ X0 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
        | ~ ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ X0 )
        | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
        | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
        | ( v1_compts_1 @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['118','163'])).

thf('165',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['117','165'])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['116','170'])).

thf('172',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['115','175'])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['176','177','178'])).

thf('180',plain,
    ( ( ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( m1_subset_1 @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['124','139'])).

thf('182',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r3_waybel_9 @ X21 @ ( sk_B_1 @ X21 ) @ X22 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('183',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ~ ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( ~ ( r3_waybel_9 @ sk_A @ ( sk_B_1 @ sk_A ) @ ( sk_B @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['180','187'])).

thf('189',plain,
    ( ( ( v1_xboole_0 @ ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('190',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('191',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('192',plain,(
    ! [X30: $i] :
      ( ( X30 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
        = o_0_0_xboole_0 ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['189','192'])).

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

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v3_yellow_6 @ X0 @ X1 )
      | ( ( k10_yellow_6 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_yellow_6])).

thf('195',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( v3_yellow_6 @ X0 @ X1 )
      | ( ( k10_yellow_6 @ X1 @ X0 )
       != o_0_0_xboole_0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['114','201'])).

thf('203',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v3_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference('sup-',[status(thm)],['90','203'])).

thf('205',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference('sup-',[status(thm)],['72','205'])).

thf('207',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference('sup-',[status(thm)],['48','207'])).

thf('209',plain,
    ( ( ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X21: $i] :
      ( ( l1_waybel_0 @ ( sk_B_1 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('211',plain,
    ( ( ( m2_yellow_6 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) @ sk_A @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('212',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ~ ( v2_struct_0 @ X7 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_waybel_0 @ ( sk_B_1 @ sk_A ) @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
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
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ ( sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X32: $i] :
        ( ( v2_struct_0 @ X32 )
        | ~ ( v4_orders_2 @ X32 )
        | ~ ( v7_waybel_0 @ X32 )
        | ~ ( l1_waybel_0 @ X32 @ sk_A )
        | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference('sup-',[status(thm)],['209','221'])).

thf('223',plain,
    ( ( ~ ( v4_orders_2 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference('sup-',[status(thm)],['5','223'])).

thf('225',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,
    ( ( ~ ( v7_waybel_0 @ ( sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference('sup-',[status(thm)],['4','228'])).

thf('230',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( ( v2_struct_0 @ ( sk_B_1 @ sk_A ) )
      | ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_B_1 @ sk_A ) ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X21: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B_1 @ X21 ) )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('237',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( ( v1_compts_1 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_compts_1 @ sk_A ) )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
      & ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X31: $i] :
      ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
      | ~ ( v3_yellow_6 @ X31 @ sk_A )
      | ~ ( v1_compts_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ~ ( v1_compts_1 @ sk_A )
   <= ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['244'])).

thf('246',plain,
    ( ~ ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( v3_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A ) )
    | ( v1_compts_1 @ sk_A )
    | ~ ! [X32: $i] :
          ( ( v2_struct_0 @ X32 )
          | ~ ( v4_orders_2 @ X32 )
          | ~ ( v7_waybel_0 @ X32 )
          | ~ ( l1_waybel_0 @ X32 @ sk_A )
          | ( m2_yellow_6 @ ( sk_C_1 @ X32 ) @ sk_A @ X32 ) ) ),
    inference('sup-',[status(thm)],['243','245'])).

thf('247',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['247'])).

thf('249',plain,
    ( ! [X31: $i] :
        ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
        | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['244'])).

thf('250',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('252',plain,
    ( ( v4_orders_2 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( v4_orders_2 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['252'])).

thf('254',plain,
    ( ~ ( v2_struct_0 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ~ ( v2_struct_0 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['254'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('256',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('257',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('258',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('259',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('260',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('261',plain,(
    ! [X21: $i,X23: $i] :
      ( ~ ( v1_compts_1 @ X21 )
      | ( r3_waybel_9 @ X21 @ X23 @ ( sk_C @ X23 @ X21 ) )
      | ~ ( l1_waybel_0 @ X23 @ X21 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('262',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( r3_waybel_9 @ sk_A @ sk_B_2 @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( r3_waybel_9 @ sk_A @ sk_B_2 @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['262','263','264'])).

thf('266',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( r3_waybel_9 @ sk_A @ sk_B_2 @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['259','265'])).

thf('267',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( r3_waybel_9 @ sk_A @ sk_B_2 @ ( sk_C @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['258','266'])).

thf('268',plain,
    ( ( ( r3_waybel_9 @ sk_A @ sk_B_2 @ ( sk_C @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['257','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( r3_waybel_9 @ sk_A @ sk_B_2 @ ( sk_C @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('272',plain,
    ( ( v1_compts_1 @ sk_A )
   <= ( v1_compts_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('273',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('274',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('275',plain,(
    ! [X21: $i,X23: $i] :
      ( ~ ( v1_compts_1 @ X21 )
      | ( m1_subset_1 @ ( sk_C @ X23 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_waybel_0 @ X23 @ X21 )
      | ~ ( v7_waybel_0 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_yellow19])).

thf('276',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_compts_1 @ sk_A ) )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,
    ( ( ~ ( v1_compts_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['273','279'])).

thf('281',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['272','280'])).

thf('282',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['271','281'])).

thf('283',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['282','283'])).

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

thf('285',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( m2_yellow_6 @ ( sk_D @ X20 @ X18 @ X19 ) @ X19 @ X18 )
      | ~ ( r3_waybel_9 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('286',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_2 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) )
        | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ X0 @ sk_A ) @ sk_A @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_2 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) )
        | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ X0 @ sk_A ) @ sk_A @ X0 )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['286','287','288'])).

thf('290',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['270','289'])).

thf('291',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('292',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('293',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('294',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['290','291','292','293'])).

thf('295',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('298',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( v4_orders_2 @ X7 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('299',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('301',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('302',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('303',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('304',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['299','300','301','302','303'])).

thf('305',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['304'])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['305','306'])).

thf('308',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('309',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( v7_waybel_0 @ X7 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('310',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['308','309'])).

thf('311',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('312',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('313',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('314',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('315',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['310','311','312','313','314'])).

thf('316',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v7_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('320',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( l1_waybel_0 @ X7 @ X5 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('321',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['319','320'])).

thf('322',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('323',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('324',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('325',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('326',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['321','322','323','324','325'])).

thf('327',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( l1_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['327','328'])).

thf('330',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( ( k10_yellow_6 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( v3_yellow_6 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_yellow_6])).

thf('331',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('332',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v7_waybel_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( ( k10_yellow_6 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( v3_yellow_6 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['330','331'])).

thf('333',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
        = o_0_0_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['329','332'])).

thf('334',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
        = o_0_0_xboole_0 )
      | ~ ( v7_waybel_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['333','334','335'])).

thf('337',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
        = o_0_0_xboole_0 )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['318','336'])).

thf('338',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
        = o_0_0_xboole_0 )
      | ~ ( v4_orders_2 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['337'])).

thf('339',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
        = o_0_0_xboole_0 )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['307','338'])).

thf('340',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['339'])).

thf('341',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( r3_waybel_9 @ sk_A @ sk_B_2 @ ( sk_C @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('342',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_C @ sk_B_2 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('343',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v7_waybel_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( r2_hidden @ X20 @ ( k10_yellow_6 @ X19 @ ( sk_D @ X20 @ X18 @ X19 ) ) )
      | ~ ( r3_waybel_9 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t32_waybel_9])).

thf('344',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_2 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ X0 @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('346',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_2 )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r3_waybel_9 @ sk_A @ X0 @ ( sk_C @ sk_B_2 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ X0 @ sk_A ) ) )
        | ~ ( l1_waybel_0 @ X0 @ sk_A )
        | ~ ( v7_waybel_0 @ X0 )
        | ~ ( v4_orders_2 @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['344','345','346'])).

thf('348',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['341','347'])).

thf('349',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('350',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('351',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('352',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['348','349','350','351'])).

thf('353',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['352'])).

thf('354',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k10_yellow_6 @ sk_A @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['353','354'])).

thf('356',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['340','355'])).

thf('357',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ o_0_0_xboole_0 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('359',plain,
    ( ! [X31: $i] :
        ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
        | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
   <= ! [X31: $i] :
        ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
        | ~ ( v3_yellow_6 @ X31 @ sk_A ) ) ),
    inference(split,[status(esa)],['244'])).

thf('360',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v3_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A ) )
   <= ( ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['358','359'])).

thf('361',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['357','360'])).

thf('362',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ o_0_0_xboole_0 ) )
   <= ( ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['361'])).

thf('363',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ( m2_yellow_6 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('364',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ~ ( v2_struct_0 @ X7 )
      | ~ ( m2_yellow_6 @ X7 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_yellow_6])).

thf('365',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
      | ~ ( v7_waybel_0 @ sk_B_2 )
      | ~ ( v4_orders_2 @ sk_B_2 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['363','364'])).

thf('366',plain,
    ( ( l1_waybel_0 @ sk_B_2 @ sk_A )
   <= ( l1_waybel_0 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['250'])).

thf('367',plain,
    ( ( v7_waybel_0 @ sk_B_2 )
   <= ( v7_waybel_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['247'])).

thf('368',plain,
    ( ( v4_orders_2 @ sk_B_2 )
   <= ( v4_orders_2 @ sk_B_2 ) ),
    inference(split,[status(esa)],['252'])).

thf('369',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('370',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['365','366','367','368','369'])).

thf('371',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['370'])).

thf('372',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('373',plain,
    ( ( ( v2_struct_0 @ sk_B_2 )
      | ~ ( v2_struct_0 @ ( sk_D @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_B_2 @ sk_A ) ) )
   <= ( ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['371','372'])).

thf('374',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_B_2 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['362','373'])).

thf('375',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ o_0_0_xboole_0 ) )
   <= ( ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['374'])).

thf('376',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_B_2 ) )
   <= ( ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['375','376'])).

thf('378',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('379',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('380',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('381',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('382',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['378','381'])).

thf('383',plain,(
    ! [X30: $i] :
      ( ( X30 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('384',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ ( k1_zfmisc_1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['382','383'])).

thf('385',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['379','380'])).

thf('386',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['384','385'])).

thf('387',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('388',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B_2 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['377','387'])).

thf('389',plain,
    ( ~ ( v2_struct_0 @ sk_B_2 )
   <= ~ ( v2_struct_0 @ sk_B_2 ) ),
    inference(split,[status(esa)],['254'])).

thf('390',plain,
    ( ! [X0: $i] :
        ~ ( v1_xboole_0 @ X0 )
   <= ( ~ ( v2_struct_0 @ sk_B_2 )
      & ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
      & ( v1_compts_1 @ sk_A )
      & ( l1_waybel_0 @ sk_B_2 @ sk_A )
      & ( v7_waybel_0 @ sk_B_2 )
      & ( v4_orders_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('391',plain,
    ( ~ ( l1_waybel_0 @ sk_B_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_B_2 )
    | ~ ( v7_waybel_0 @ sk_B_2 )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ! [X31: $i] :
          ( ~ ( m2_yellow_6 @ X31 @ sk_A @ sk_B_2 )
          | ~ ( v3_yellow_6 @ X31 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['256','390'])).

thf('392',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','246','248','249','251','253','255','391'])).


%------------------------------------------------------------------------------
