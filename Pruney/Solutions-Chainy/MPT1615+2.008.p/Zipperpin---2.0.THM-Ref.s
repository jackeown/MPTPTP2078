%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nADkrftsCE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 157 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X3 ) )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X4 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X4 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X4 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X4 ) ) ),
    inference(clc,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nADkrftsCE
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 8 iterations in 0.008s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.46  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.46  thf(t5_pre_topc, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X3 : $i]:
% 0.20/0.46         ((r2_hidden @ k1_xboole_0 @ (u1_pre_topc @ X3))
% 0.20/0.46          | ~ (l1_pre_topc @ X3)
% 0.20/0.46          | ~ (v2_pre_topc @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t5_pre_topc])).
% 0.20/0.46  thf(t13_yellow_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.46       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.20/0.46         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X4 : $i]:
% 0.20/0.46         (~ (r2_hidden @ k1_xboole_0 @ X4)
% 0.20/0.46          | ((k3_yellow_0 @ (k2_yellow_1 @ X4)) = (k1_xboole_0))
% 0.20/0.46          | (v1_xboole_0 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.20/0.46  thf(d1_xboole_0, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X4 : $i]:
% 0.20/0.46         (((k3_yellow_0 @ (k2_yellow_1 @ X4)) = (k1_xboole_0))
% 0.20/0.46          | ~ (r2_hidden @ k1_xboole_0 @ X4))),
% 0.20/0.46      inference('clc', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v2_pre_topc @ X0)
% 0.20/0.46          | ~ (l1_pre_topc @ X0)
% 0.20/0.46          | ((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0))) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.46  thf(t23_yellow_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.46       ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.46         ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.46            ( l1_pre_topc @ A ) ) =>
% 0.20/0.46          ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.20/0.46            ( k1_xboole_0 ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t23_yellow_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (((k3_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A))) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.46        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('9', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.46  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
