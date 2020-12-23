%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UlBf7MvbvI

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  51 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  240 ( 288 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t91_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X14 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_xboole_0 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ( X17 = X18 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('18',plain,(
    ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UlBf7MvbvI
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:30:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 195 iterations in 0.071s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(t91_relat_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.58         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i]:
% 0.21/0.58        ( ( v1_relat_1 @ B ) =>
% 0.21/0.58          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.58            ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t91_relat_1])).
% 0.21/0.58  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t36_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.21/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.58  thf(t1_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.58       ( r1_tarski @ A @ C ) ))).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.58         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.58          | ~ (r1_tarski @ X6 @ X7)
% 0.21/0.58          | (r1_tarski @ X5 @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.58  thf(t79_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.21/0.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.58  thf(t69_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.58       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i]:
% 0.21/0.58         (~ (r1_xboole_0 @ X13 @ X14)
% 0.21/0.58          | ~ (r1_tarski @ X13 @ X14)
% 0.21/0.58          | (v1_xboole_0 @ X13))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.58          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.58  thf('8', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.58  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf(t8_boole, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         (~ (v1_xboole_0 @ X17) | ~ (v1_xboole_0 @ X18) | ((X17) = (X18)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t8_boole])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.58  thf(t48_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.21/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.58         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf(t3_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('15', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf('16', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf(t90_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.58         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X19 : $i, X20 : $i]:
% 0.21/0.58         (((k1_relat_1 @ (k7_relat_1 @ X19 @ X20))
% 0.21/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X19) @ X20))
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.58  thf('18', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) != (sk_A))
% 0.21/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.58  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('22', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) != (sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.58  thf('23', plain, ($false),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['16', '22'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
