%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lV3MXetoav

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  37 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  125 ( 221 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X2 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X2 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['7'])).

thf(fc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc1_pre_topc])).

thf('10',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lV3MXetoav
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.43  % Solved by: fo/fo7.sh
% 0.21/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.43  % done 8 iterations in 0.008s
% 0.21/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.43  % SZS output start Refutation
% 0.21/0.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.43  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.43  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.43  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.43  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.43  thf(t5_pre_topc, axiom,
% 0.21/0.43    (![A:$i]:
% 0.21/0.43     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.43       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.21/0.43  thf('0', plain,
% 0.21/0.43      (![X1 : $i]:
% 0.21/0.43         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X1))
% 0.21/0.43          | ~ (l1_pre_topc @ X1)
% 0.21/0.43          | ~ (v2_pre_topc @ X1))),
% 0.21/0.43      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.21/0.43  thf(t13_yellow_1, axiom,
% 0.21/0.43    (![A:$i]:
% 0.21/0.43     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.43       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.43         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.43  thf('1', plain,
% 0.21/0.43      (![X2 : $i]:
% 0.21/0.43         (~ (r2_hidden @ k1_xboole_0 @ X2)
% 0.21/0.43          | ((k3_yellow_0 @ (k2_yellow_1 @ X2)) = (k1_xboole_0))
% 0.21/0.43          | (v1_xboole_0 @ X2))),
% 0.21/0.43      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.21/0.43  thf('2', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         (~ (v2_pre_topc @ X0)
% 0.21/0.43          | ~ (l1_pre_topc @ X0)
% 0.21/0.43          | (v1_xboole_0 @ (u1_pre_topc @ X0))
% 0.21/0.43          | ((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0)))),
% 0.21/0.43      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.43  thf(t23_yellow_1, conjecture,
% 0.21/0.43    (![A:$i]:
% 0.21/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.43       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.43         ( k1_xboole_0 ) ) ))).
% 0.21/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.43    (~( ![A:$i]:
% 0.21/0.43        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.43            ( l1_pre_topc @ A ) ) =>
% 0.21/0.43          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.43            ( k1_xboole_0 ) ) ) )),
% 0.21/0.43    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.21/0.43  thf('3', plain,
% 0.21/0.43      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('4', plain,
% 0.21/0.43      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.43        | (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.21/0.43        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.43        | ~ (v2_pre_topc @ sk_A))),
% 0.21/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.43  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('7', plain,
% 0.21/0.43      ((((k1_xboole_0) != (k1_xboole_0)) | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.21/0.43      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.43  thf('8', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 0.21/0.43      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.43  thf(fc1_pre_topc, axiom,
% 0.21/0.43    (![A:$i]:
% 0.21/0.43     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.43       ( ~( v1_xboole_0 @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.43  thf('9', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         (~ (v1_xboole_0 @ (u1_pre_topc @ X0))
% 0.21/0.43          | ~ (l1_pre_topc @ X0)
% 0.21/0.43          | ~ (v2_pre_topc @ X0))),
% 0.21/0.43      inference('cnf', [status(esa)], [fc1_pre_topc])).
% 0.21/0.43  thf('10', plain, ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.43      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.43  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('13', plain, ($false),
% 0.21/0.43      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.43  
% 0.21/0.43  % SZS output end Refutation
% 0.21/0.43  
% 0.21/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
