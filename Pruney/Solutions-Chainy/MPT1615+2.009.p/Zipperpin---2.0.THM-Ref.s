%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qN7ysQycQb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  48 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 244 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X4 ) )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X8 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X8 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X8 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X8 ) ) ),
    inference(clc,[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t23_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t23_yellow_1])).

thf('13',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qN7ysQycQb
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:28:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 32 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.47  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.47  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.47  thf(t5_pre_topc, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X4 : $i]:
% 0.21/0.47         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X4))
% 0.21/0.47          | ~ (l1_pre_topc @ X4)
% 0.21/0.47          | ~ (v2_pre_topc @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.21/0.47  thf(t13_yellow_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.47         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X8 : $i]:
% 0.21/0.47         (~ (r2_hidden @ k1_xboole_0 @ X8)
% 0.21/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ X8)) = (k1_xboole_0))
% 0.21/0.47          | (v1_xboole_0 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.21/0.47  thf(t1_yellow_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.47       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.47  thf('2', plain, (![X9 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X9)) = (X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.47  thf(dt_k3_yellow_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X5 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k3_yellow_0 @ X5) @ (u1_struct_0 @ X5))
% 0.21/0.47          | ~ (l1_orders_2 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)
% 0.21/0.47          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(dt_k2_yellow_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.47       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.47  thf('5', plain, (![X7 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]: (m1_subset_1 @ (k3_yellow_0 @ (k2_yellow_1 @ X0)) @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(d2_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X3 @ X2) | (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0)
% 0.21/0.47          | (v1_xboole_0 @ (k3_yellow_0 @ (k2_yellow_1 @ X0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf(l13_xboole_0, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ X0)
% 0.21/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ X0)) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X8 : $i]:
% 0.21/0.47         (((k3_yellow_0 @ (k2_yellow_1 @ X8)) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ k1_xboole_0 @ X8))),
% 0.21/0.47      inference('clc', [status(thm)], ['1', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v2_pre_topc @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0)
% 0.21/0.47          | ((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.47  thf(t23_yellow_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.47         ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.47            ( k1_xboole_0 ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | ~ (v2_pre_topc @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.47  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
