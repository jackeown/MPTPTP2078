%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VPCiMlKkVQ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 224 expanded)
%              Number of leaves         :   28 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  840 (3493 expanded)
%              Number of equality atoms :   15 ( 109 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(o_2_2_yellow_6_type,type,(
    o_2_2_yellow_6: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t45_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( k11_yellow_6 @ A @ B )
            = ( k4_yellow_6 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v8_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A )
              & ( l1_waybel_0 @ B @ A ) )
           => ( ( k11_yellow_6 @ A @ B )
              = ( k4_yellow_6 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_yellow_6])).

thf('0',plain,(
    v1_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v7_waybel_0 @ X14 )
      | ~ ( v1_yellow_6 @ X14 @ X15 )
      | ~ ( l1_waybel_0 @ X14 @ X15 )
      | ( r2_hidden @ ( k4_yellow_6 @ X15 @ X14 ) @ ( k10_yellow_6 @ X15 @ X14 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_6])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4','5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(d20_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v8_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v3_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( C
                  = ( k11_yellow_6 @ A @ B ) )
              <=> ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v4_orders_2 @ X6 )
      | ~ ( v7_waybel_0 @ X6 )
      | ~ ( v3_yellow_6 @ X6 @ X7 )
      | ~ ( l1_waybel_0 @ X6 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k10_yellow_6 @ X7 @ X6 ) )
      | ( X8
        = ( k11_yellow_6 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v8_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d20_yellow_6])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_yellow_6 @ sk_A @ sk_B )
      = ( k11_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v3_yellow_6 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v1_yellow_6 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( v3_yellow_6 @ B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_waybel_0 @ X4 @ X5 )
      | ( v3_yellow_6 @ X4 @ X5 )
      | ~ ( v1_yellow_6 @ X4 @ X5 )
      | ~ ( v7_waybel_0 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_6])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v1_yellow_6 @ sk_B @ sk_A )
    | ( v3_yellow_6 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v3_yellow_6 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23','24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v3_yellow_6 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_yellow_6 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_yellow_6 @ sk_A @ sk_B )
      = ( k11_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16','17','18','31','32','33'])).

thf('35',plain,(
    ( k11_yellow_6 @ sk_A @ sk_B )
 != ( k4_yellow_6 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ~ ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_o_2_2_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v4_orders_2 @ B )
        & ( v7_waybel_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v7_waybel_0 @ X10 )
      | ~ ( l1_waybel_0 @ X10 @ X9 )
      | ( m1_subset_1 @ ( o_2_2_yellow_6 @ X9 @ X10 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_2_yellow_6])).

thf('44',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(dt_k2_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_waybel_0 @ X1 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( k2_waybel_0 @ X2 @ X1 @ X3 ) @ ( u1_struct_0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_waybel_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_waybel_0 @ X0 @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf(t25_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( v1_yellow_6 @ B @ A )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( k2_waybel_0 @ A @ B @ C )
                = ( k4_yellow_6 @ A @ B ) ) ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v7_waybel_0 @ X11 )
      | ~ ( v1_yellow_6 @ X11 @ X12 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ( ( k2_waybel_0 @ X12 @ X11 @ X13 )
        = ( k4_yellow_6 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_6])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_waybel_0 @ X0 @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) )
        = ( k4_yellow_6 @ X0 @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ~ ( v1_yellow_6 @ sk_B @ X0 )
      | ~ ( v7_waybel_0 @ sk_B )
      | ~ ( v4_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_waybel_0 @ X0 @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) )
        = ( k4_yellow_6 @ X0 @ sk_B ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ~ ( v1_yellow_6 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v1_yellow_6 @ sk_B @ sk_A )
    | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) )
      = ( k4_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    v1_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) )
      = ( k4_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) )
      = ( k4_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_waybel_0 @ sk_A @ sk_B @ ( o_2_2_yellow_6 @ sk_A @ sk_B ) )
    = ( k4_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['40','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VPCiMlKkVQ
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:46:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 31 iterations in 0.021s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.20/0.47  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.20/0.47  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.20/0.47  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.20/0.47  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.47  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.20/0.47  thf(o_2_2_yellow_6_type, type, o_2_2_yellow_6: $i > $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(t45_yellow_6, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.47             ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47           ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47                ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.47                ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47              ( ( k11_yellow_6 @ A @ B ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t45_yellow_6])).
% 0.20/0.47  thf('0', plain, ((v1_yellow_6 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t42_yellow_6, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.47             ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X14)
% 0.20/0.47          | ~ (v4_orders_2 @ X14)
% 0.20/0.47          | ~ (v7_waybel_0 @ X14)
% 0.20/0.47          | ~ (v1_yellow_6 @ X14 @ X15)
% 0.20/0.47          | ~ (l1_waybel_0 @ X14 @ X15)
% 0.20/0.47          | (r2_hidden @ (k4_yellow_6 @ X15 @ X14) @ (k10_yellow_6 @ X15 @ X14))
% 0.20/0.47          | ~ (l1_pre_topc @ X15)
% 0.20/0.47          | ~ (v2_pre_topc @ X15)
% 0.20/0.47          | (v2_struct_0 @ X15))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_yellow_6])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.47           (k10_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.47           (k10_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3', '4', '5', '6', '7'])).
% 0.20/0.47  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.47           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(d20_yellow_6, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47         ( v8_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47             ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) & 
% 0.20/0.47             ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.47               ( ( ( C ) = ( k11_yellow_6 @ A @ B ) ) <=>
% 0.20/0.47                 ( r2_hidden @ C @ ( k10_yellow_6 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X6)
% 0.20/0.47          | ~ (v4_orders_2 @ X6)
% 0.20/0.47          | ~ (v7_waybel_0 @ X6)
% 0.20/0.47          | ~ (v3_yellow_6 @ X6 @ X7)
% 0.20/0.47          | ~ (l1_waybel_0 @ X6 @ X7)
% 0.20/0.47          | ~ (r2_hidden @ X8 @ (k10_yellow_6 @ X7 @ X6))
% 0.20/0.47          | ((X8) = (k11_yellow_6 @ X7 @ X6))
% 0.20/0.47          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.47          | ~ (l1_pre_topc @ X7)
% 0.20/0.47          | ~ (v8_pre_topc @ X7)
% 0.20/0.47          | ~ (v2_pre_topc @ X7)
% 0.20/0.47          | (v2_struct_0 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [d20_yellow_6])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (v8_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ((k4_yellow_6 @ sk_A @ sk_B) = (k11_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (v3_yellow_6 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, ((v8_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc4_yellow_6, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( l1_waybel_0 @ B @ A ) =>
% 0.20/0.47           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47               ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) ) =>
% 0.20/0.47             ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47               ( v7_waybel_0 @ B ) & ( v3_yellow_6 @ B @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (l1_waybel_0 @ X4 @ X5)
% 0.20/0.47          | (v3_yellow_6 @ X4 @ X5)
% 0.20/0.47          | ~ (v1_yellow_6 @ X4 @ X5)
% 0.20/0.47          | ~ (v7_waybel_0 @ X4)
% 0.20/0.47          | ~ (v4_orders_2 @ X4)
% 0.20/0.47          | (v2_struct_0 @ X4)
% 0.20/0.47          | ~ (l1_pre_topc @ X5)
% 0.20/0.47          | ~ (v2_pre_topc @ X5)
% 0.20/0.47          | (v2_struct_0 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc4_yellow_6])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.47        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.47        | ~ (v1_yellow_6 @ sk_B @ sk_A)
% 0.20/0.47        | (v3_yellow_6 @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain, ((v1_yellow_6 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (v3_yellow_6 @ sk_B @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '22', '23', '24', '25', '26'])).
% 0.20/0.47  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, (((v3_yellow_6 @ sk_B @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | ((k4_yellow_6 @ sk_A @ sk_B) = (k11_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['14', '15', '16', '17', '18', '31', '32', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (((k11_yellow_6 @ sk_A @ sk_B) != (k4_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | ~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.47  thf('39', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (~ (m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.47  thf('41', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('42', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_o_2_2_yellow_6, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.47         ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47         ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( o_2_2_yellow_6 @ A @ B ) @ ( u1_struct_0 @ B ) ) ))).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (l1_struct_0 @ X9)
% 0.20/0.47          | (v2_struct_0 @ X9)
% 0.20/0.47          | (v2_struct_0 @ X10)
% 0.20/0.47          | ~ (v4_orders_2 @ X10)
% 0.20/0.47          | ~ (v7_waybel_0 @ X10)
% 0.20/0.47          | ~ (l1_waybel_0 @ X10 @ X9)
% 0.20/0.47          | (m1_subset_1 @ (o_2_2_yellow_6 @ X9 @ X10) @ (u1_struct_0 @ X10)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_o_2_2_yellow_6])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.20/0.47        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_l1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.47  thf('48', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.47  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      (((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['44', '45', '46', '49'])).
% 0.20/0.47  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.47  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.47  thf(dt_k2_waybel_0, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.47         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.20/0.47         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k2_waybel_0 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.47         (~ (l1_waybel_0 @ X1 @ X2)
% 0.20/0.47          | (v2_struct_0 @ X1)
% 0.20/0.47          | ~ (l1_struct_0 @ X2)
% 0.20/0.47          | (v2_struct_0 @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.47          | (m1_subset_1 @ (k2_waybel_0 @ X2 @ X1 @ X3) @ (u1_struct_0 @ X2)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k2_waybel_0])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ 
% 0.20/0.47           (k2_waybel_0 @ X0 @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B)) @ 
% 0.20/0.47           (u1_struct_0 @ X0))
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_struct_0 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.47  thf('57', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | (m1_subset_1 @ 
% 0.20/0.47           (k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B)) @ 
% 0.20/0.47           (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['41', '56'])).
% 0.20/0.47  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('59', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | (m1_subset_1 @ 
% 0.20/0.47           (k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B)) @ 
% 0.20/0.47           (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.47  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('61', plain,
% 0.20/0.47      (((m1_subset_1 @ 
% 0.20/0.47         (k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B)) @ 
% 0.20/0.47         (u1_struct_0 @ sk_A))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.47  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('63', plain,
% 0.20/0.47      ((m1_subset_1 @ 
% 0.20/0.47        (k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B)) @ 
% 0.20/0.47        (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.47  thf('64', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('65', plain,
% 0.20/0.47      ((m1_subset_1 @ (o_2_2_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.47  thf(t25_yellow_6, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.47             ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47               ( ( k2_waybel_0 @ A @ B @ C ) = ( k4_yellow_6 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('66', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X11)
% 0.20/0.47          | ~ (v4_orders_2 @ X11)
% 0.20/0.47          | ~ (v7_waybel_0 @ X11)
% 0.20/0.47          | ~ (v1_yellow_6 @ X11 @ X12)
% 0.20/0.47          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.20/0.47          | ((k2_waybel_0 @ X12 @ X11 @ X13) = (k4_yellow_6 @ X12 @ X11))
% 0.20/0.47          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.20/0.47          | ~ (l1_struct_0 @ X12)
% 0.20/0.47          | (v2_struct_0 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t25_yellow_6])).
% 0.20/0.47  thf('67', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_struct_0 @ X0)
% 0.20/0.47          | ((k2_waybel_0 @ X0 @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47              = (k4_yellow_6 @ X0 @ sk_B))
% 0.20/0.47          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.20/0.47          | ~ (v1_yellow_6 @ sk_B @ X0)
% 0.20/0.47          | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.47          | ~ (v4_orders_2 @ sk_B)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.47  thf('68', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('69', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('70', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_struct_0 @ X0)
% 0.20/0.47          | ((k2_waybel_0 @ X0 @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47              = (k4_yellow_6 @ X0 @ sk_B))
% 0.20/0.47          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.20/0.47          | ~ (v1_yellow_6 @ sk_B @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.20/0.47  thf('71', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | ~ (v1_yellow_6 @ sk_B @ sk_A)
% 0.20/0.47        | ((k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47            = (k4_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['64', '70'])).
% 0.20/0.47  thf('72', plain, ((v1_yellow_6 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('74', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | ((k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47            = (k4_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.20/0.47  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('76', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47            = (k4_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.47  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('78', plain,
% 0.20/0.47      (((k2_waybel_0 @ sk_A @ sk_B @ (o_2_2_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47         = (k4_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.47  thf('79', plain,
% 0.20/0.47      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['63', '78'])).
% 0.20/0.47  thf('80', plain, ($false), inference('demod', [status(thm)], ['40', '79'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
