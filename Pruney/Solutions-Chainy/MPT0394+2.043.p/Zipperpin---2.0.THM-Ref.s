%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9HcEwbPlBa

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:50 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 100 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  348 ( 749 expanded)
%              Number of equality atoms :   49 ( 107 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X16 @ X16 @ X17 @ X18 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

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

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) )
      | ( X21 != X22 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X22: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X22: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','24'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9HcEwbPlBa
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:25:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 522 iterations in 0.305s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.77  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.59/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.59/0.77  thf(t70_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i]:
% 0.59/0.77         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.59/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.77  thf(t69_enumset1, axiom,
% 0.59/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.77  thf('1', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.59/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf(t46_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.77       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.77         ((k2_enumset1 @ X9 @ X10 @ X11 @ X12)
% 0.59/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.59/0.77           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf(t71_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.77         ((k2_enumset1 @ X16 @ X16 @ X17 @ X18)
% 0.59/0.77           = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i]:
% 0.59/0.77         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.59/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.59/0.77           = (k2_tarski @ X1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['4', '7'])).
% 0.59/0.77  thf(t11_setfam_1, axiom,
% 0.59/0.77    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.59/0.77  thf('9', plain, (![X25 : $i]: ((k1_setfam_1 @ (k1_tarski @ X25)) = (X25))),
% 0.59/0.77      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.59/0.77  thf(t10_setfam_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.77          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.59/0.77            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X23 : $i, X24 : $i]:
% 0.59/0.77         (((X23) = (k1_xboole_0))
% 0.59/0.77          | ((k1_setfam_1 @ (k2_xboole_0 @ X23 @ X24))
% 0.59/0.77              = (k3_xboole_0 @ (k1_setfam_1 @ X23) @ (k1_setfam_1 @ X24)))
% 0.59/0.77          | ((X24) = (k1_xboole_0)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.59/0.77            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.59/0.77          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.59/0.77          | ((X1) = (k1_xboole_0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.59/0.77            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.59/0.77          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.59/0.77          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['8', '11'])).
% 0.59/0.77  thf('13', plain, (![X25 : $i]: ((k1_setfam_1 @ (k1_tarski @ X25)) = (X25))),
% 0.59/0.77      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.59/0.77          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf(t12_setfam_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i]:
% 0.59/0.77        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.59/0.77         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.59/0.77        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.59/0.77        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.59/0.77        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['16'])).
% 0.59/0.77  thf(t16_zfmisc_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.59/0.77          ( ( A ) = ( B ) ) ) ))).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X21 : $i, X22 : $i]:
% 0.59/0.77         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22))
% 0.59/0.77          | ((X21) != (X22)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X22 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.59/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.59/0.77        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['17', '19'])).
% 0.59/0.77  thf(t2_boole, axiom,
% 0.59/0.77    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.59/0.77  thf(d7_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X2 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.77  thf('24', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.77  thf('25', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['20', '24'])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X22 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.59/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.77  thf('27', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.59/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.77  thf('28', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['20', '24'])).
% 0.59/0.77  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.77  thf('30', plain, ($false),
% 0.59/0.77      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
