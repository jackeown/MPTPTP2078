%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z3YzESuo0n

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:49 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 160 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  379 (1355 expanded)
%              Number of equality atoms :   55 ( 197 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X16 @ X16 @ X17 @ X18 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X23 @ X24 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X23 ) @ ( k1_setfam_1 @ X24 ) ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X25: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) )
      | ( X21 != X22 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('20',plain,(
    ! [X22: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X22: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('30',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('32',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z3YzESuo0n
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.64  % Solved by: fo/fo7.sh
% 0.47/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.64  % done 441 iterations in 0.185s
% 0.47/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.64  % SZS output start Refutation
% 0.47/0.64  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.47/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.47/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.64  thf(t69_enumset1, axiom,
% 0.47/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.64  thf('0', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.47/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.64  thf(t71_enumset1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i]:
% 0.47/0.64     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.47/0.64  thf('1', plain,
% 0.47/0.64      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.64         ((k2_enumset1 @ X16 @ X16 @ X17 @ X18)
% 0.47/0.64           = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.47/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.47/0.64  thf(t70_enumset1, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.47/0.64  thf('2', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i]:
% 0.47/0.64         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.64  thf('3', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.47/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.64  thf('4', plain,
% 0.47/0.64      (![X14 : $i, X15 : $i]:
% 0.47/0.64         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.47/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.47/0.64  thf(t46_enumset1, axiom,
% 0.47/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.64     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.47/0.64       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.47/0.64  thf('5', plain,
% 0.47/0.64      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.64         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 0.47/0.64           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ (k1_tarski @ X7)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.47/0.64  thf('6', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.64         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.47/0.64           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['4', '5'])).
% 0.47/0.64  thf('7', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k2_tarski @ X1 @ X0)
% 0.47/0.64           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['3', '6'])).
% 0.47/0.64  thf('8', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         ((k2_tarski @ X0 @ X1)
% 0.47/0.64           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['0', '7'])).
% 0.47/0.64  thf(t11_setfam_1, axiom,
% 0.47/0.64    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.47/0.64  thf('9', plain, (![X25 : $i]: ((k1_setfam_1 @ (k1_tarski @ X25)) = (X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.64  thf(t10_setfam_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.64          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.47/0.64            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.47/0.64  thf('10', plain,
% 0.47/0.64      (![X23 : $i, X24 : $i]:
% 0.47/0.64         (((X23) = (k1_xboole_0))
% 0.47/0.64          | ((k1_setfam_1 @ (k2_xboole_0 @ X23 @ X24))
% 0.47/0.64              = (k3_xboole_0 @ (k1_setfam_1 @ X23) @ (k1_setfam_1 @ X24)))
% 0.47/0.64          | ((X24) = (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.47/0.64  thf('11', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.47/0.64            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.47/0.64          | ((X1) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.64  thf('12', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.47/0.64            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.47/0.64          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup+', [status(thm)], ['8', '11'])).
% 0.47/0.64  thf('13', plain, (![X25 : $i]: ((k1_setfam_1 @ (k1_tarski @ X25)) = (X25))),
% 0.47/0.64      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.64  thf('14', plain,
% 0.47/0.64      (![X0 : $i, X1 : $i]:
% 0.47/0.64         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.47/0.64          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.47/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['12', '13'])).
% 0.47/0.64  thf(t12_setfam_1, conjecture,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.64    (~( ![A:$i,B:$i]:
% 0.47/0.64        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.47/0.64    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.47/0.64  thf('15', plain,
% 0.47/0.64      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.47/0.64         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.64  thf('16', plain,
% 0.47/0.64      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.64  thf('17', plain,
% 0.47/0.64      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf('18', plain,
% 0.47/0.64      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.47/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.47/0.64  thf(t16_zfmisc_1, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.47/0.64          ( ( A ) = ( B ) ) ) ))).
% 0.47/0.64  thf('19', plain,
% 0.47/0.64      (![X21 : $i, X22 : $i]:
% 0.47/0.64         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22))
% 0.47/0.64          | ((X21) != (X22)))),
% 0.47/0.64      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.47/0.64  thf('20', plain,
% 0.47/0.64      (![X22 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.47/0.64      inference('simplify', [status(thm)], ['19'])).
% 0.47/0.64  thf('21', plain,
% 0.47/0.64      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.47/0.64        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['18', '20'])).
% 0.47/0.64  thf('22', plain,
% 0.47/0.64      ((~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.47/0.64        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('sup-', [status(thm)], ['17', '21'])).
% 0.47/0.64  thf(idempotence_k3_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.47/0.64  thf('23', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.47/0.64      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.47/0.64  thf(d7_xboole_0, axiom,
% 0.47/0.64    (![A:$i,B:$i]:
% 0.47/0.64     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.47/0.64       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.64  thf('24', plain,
% 0.47/0.64      (![X0 : $i, X2 : $i]:
% 0.47/0.64         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.47/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.64  thf('25', plain,
% 0.47/0.64      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.47/0.64      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.64  thf('26', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('simplify', [status(thm)], ['25'])).
% 0.47/0.64  thf('27', plain,
% 0.47/0.64      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.47/0.64        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.47/0.64      inference('demod', [status(thm)], ['22', '26'])).
% 0.47/0.64  thf('28', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['27'])).
% 0.47/0.64  thf('29', plain,
% 0.47/0.64      (![X22 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.47/0.64      inference('simplify', [status(thm)], ['19'])).
% 0.47/0.64  thf('30', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.47/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.64  thf('31', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.47/0.64      inference('simplify', [status(thm)], ['27'])).
% 0.47/0.64  thf('32', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.47/0.64      inference('simplify', [status(thm)], ['25'])).
% 0.47/0.64  thf('33', plain, ($false),
% 0.47/0.64      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
