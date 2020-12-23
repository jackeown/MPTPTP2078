%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sWCf0tkOCy

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 129 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  480 (1938 expanded)
%              Number of equality atoms :    7 (  61 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_yellow_6_type,type,(
    v1_yellow_6: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_yellow_6_type,type,(
    k10_yellow_6: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_yellow_6_type,type,(
    v3_yellow_6: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k11_yellow_6_type,type,(
    k11_yellow_6: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_yellow_6_type,type,(
    k4_yellow_6: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v7_waybel_0 @ X8 )
      | ~ ( v1_yellow_6 @ X8 @ X9 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( r2_hidden @ ( k4_yellow_6 @ X9 @ X8 ) @ ( k10_yellow_6 @ X9 @ X8 ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t42_yellow_6])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6','7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( k10_yellow_6 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ~ ( v7_waybel_0 @ X3 )
      | ~ ( v3_yellow_6 @ X3 @ X4 )
      | ~ ( l1_waybel_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k10_yellow_6 @ X4 @ X3 ) )
      | ( X5
        = ( k11_yellow_6 @ X4 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v8_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d20_yellow_6])).

thf('15',plain,
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
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_waybel_0 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k4_yellow_6 @ X6 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_yellow_6])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k4_yellow_6 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_waybel_0 @ X1 @ X2 )
      | ( v3_yellow_6 @ X1 @ X2 )
      | ~ ( v1_yellow_6 @ X1 @ X2 )
      | ~ ( v7_waybel_0 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc4_yellow_6])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v4_orders_2 @ sk_B )
    | ~ ( v7_waybel_0 @ sk_B )
    | ~ ( v1_yellow_6 @ sk_B @ sk_A )
    | ( v3_yellow_6 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_yellow_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v3_yellow_6 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33','34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v3_yellow_6 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_yellow_6 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    v7_waybel_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_yellow_6 @ sk_A @ sk_B )
      = ( k11_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16','17','18','27','28','41','42','43'])).

thf('45',plain,(
    ( k11_yellow_6 @ sk_A @ sk_B )
 != ( k4_yellow_6 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sWCf0tkOCy
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 22 iterations in 0.015s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(v1_yellow_6_type, type, v1_yellow_6: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k10_yellow_6_type, type, k10_yellow_6: $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v3_yellow_6_type, type, v3_yellow_6: $i > $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(k11_yellow_6_type, type, k11_yellow_6: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k4_yellow_6_type, type, k4_yellow_6: $i > $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.20/0.47  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
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
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((v1_yellow_6 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t42_yellow_6, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.47             ( v7_waybel_0 @ B ) & ( v1_yellow_6 @ B @ A ) & 
% 0.20/0.47             ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47           ( r2_hidden @ ( k4_yellow_6 @ A @ B ) @ ( k10_yellow_6 @ A @ B ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X8)
% 0.20/0.47          | ~ (v4_orders_2 @ X8)
% 0.20/0.47          | ~ (v7_waybel_0 @ X8)
% 0.20/0.47          | ~ (v1_yellow_6 @ X8 @ X9)
% 0.20/0.47          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.47          | (r2_hidden @ (k4_yellow_6 @ X9 @ X8) @ (k10_yellow_6 @ X9 @ X8))
% 0.20/0.47          | ~ (l1_pre_topc @ X9)
% 0.20/0.47          | ~ (v2_pre_topc @ X9)
% 0.20/0.47          | (v2_struct_0 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_yellow_6])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.47           (k10_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.47        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.47           (k10_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4', '5', '6', '7', '8'])).
% 0.20/0.47  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | (r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ 
% 0.20/0.47           (k10_yellow_6 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((r2_hidden @ (k4_yellow_6 @ sk_A @ sk_B) @ (k10_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['11', '12'])).
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
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X3)
% 0.20/0.47          | ~ (v4_orders_2 @ X3)
% 0.20/0.47          | ~ (v7_waybel_0 @ X3)
% 0.20/0.47          | ~ (v3_yellow_6 @ X3 @ X4)
% 0.20/0.47          | ~ (l1_waybel_0 @ X3 @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X5 @ (k10_yellow_6 @ X4 @ X3))
% 0.20/0.47          | ((X5) = (k11_yellow_6 @ X4 @ X3))
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.20/0.47          | ~ (l1_pre_topc @ X4)
% 0.20/0.47          | ~ (v8_pre_topc @ X4)
% 0.20/0.47          | ~ (v2_pre_topc @ X4)
% 0.20/0.47          | (v2_struct_0 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d20_yellow_6])).
% 0.20/0.47  thf('15', plain,
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
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, ((v8_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k4_yellow_6, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.47         ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k4_yellow_6 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (l1_struct_0 @ X6)
% 0.20/0.47          | (v2_struct_0 @ X6)
% 0.20/0.47          | ~ (l1_waybel_0 @ X7 @ X6)
% 0.20/0.47          | (m1_subset_1 @ (k4_yellow_6 @ X6 @ X7) @ (u1_struct_0 @ X6)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k4_yellow_6])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_l1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.47  thf('23', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.47  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.47  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((m1_subset_1 @ (k4_yellow_6 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.47  thf('28', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
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
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (l1_waybel_0 @ X1 @ X2)
% 0.20/0.47          | (v3_yellow_6 @ X1 @ X2)
% 0.20/0.47          | ~ (v1_yellow_6 @ X1 @ X2)
% 0.20/0.47          | ~ (v7_waybel_0 @ X1)
% 0.20/0.47          | ~ (v4_orders_2 @ X1)
% 0.20/0.47          | (v2_struct_0 @ X1)
% 0.20/0.47          | ~ (l1_pre_topc @ X2)
% 0.20/0.47          | ~ (v2_pre_topc @ X2)
% 0.20/0.47          | (v2_struct_0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc4_yellow_6])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | ~ (v4_orders_2 @ sk_B)
% 0.20/0.47        | ~ (v7_waybel_0 @ sk_B)
% 0.20/0.47        | ~ (v1_yellow_6 @ sk_B @ sk_A)
% 0.20/0.47        | (v3_yellow_6 @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('36', plain, ((v1_yellow_6 @ sk_B @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (v2_struct_0 @ sk_B)
% 0.20/0.47        | (v3_yellow_6 @ sk_B @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['31', '32', '33', '34', '35', '36'])).
% 0.20/0.47  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, (((v3_yellow_6 @ sk_B @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain, ((v3_yellow_6 @ sk_B @ sk_A)),
% 0.20/0.47      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain, ((v7_waybel_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('43', plain, ((v4_orders_2 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((k4_yellow_6 @ sk_A @ sk_B) = (k11_yellow_6 @ sk_A @ sk_B))
% 0.20/0.47        | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['15', '16', '17', '18', '27', '28', '41', '42', '43'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (((k11_yellow_6 @ sk_A @ sk_B) != (k4_yellow_6 @ sk_A @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('48', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.47  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
