%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xZ5e4mECpa

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   48 (  51 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  298 ( 319 expanded)
%              Number of equality atoms :   37 (  40 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xZ5e4mECpa
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 404 iterations in 0.230s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(t70_enumset1, conjecture,
% 0.47/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(t41_enumset1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( k2_tarski @ A @ B ) =
% 0.47/0.68       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X15 : $i, X16 : $i]:
% 0.47/0.68         ((k2_tarski @ X15 @ X16)
% 0.47/0.68           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.47/0.68  thf(t21_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.47/0.68      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.47/0.68           = (k1_tarski @ X1))),
% 0.47/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k3_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 0.47/0.68           = (k1_tarski @ X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['3', '4'])).
% 0.47/0.68  thf(t100_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (![X4 : $i, X5 : $i]:
% 0.47/0.68         ((k4_xboole_0 @ X4 @ X5)
% 0.47/0.68           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.68  thf(commutativity_k5_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.68  thf(t92_xboole_1, axiom,
% 0.47/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.68  thf('8', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.68  thf(t91_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.47/0.68       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.47/0.68  thf('9', plain,
% 0.47/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.68         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.47/0.68           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.47/0.68           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.68  thf(t5_boole, axiom,
% 0.47/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.68  thf('12', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.47/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.68  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.47/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['10', '13'])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.47/0.68      inference('sup+', [status(thm)], ['7', '14'])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((X1)
% 0.47/0.68           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.47/0.68      inference('sup+', [status(thm)], ['6', '15'])).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((X1)
% 0.47/0.68           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k2_tarski @ X0 @ X1)
% 0.47/0.68           = (k5_xboole_0 @ 
% 0.47/0.68              (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)) @ 
% 0.47/0.68              (k1_tarski @ X0)))),
% 0.47/0.68      inference('sup+', [status(thm)], ['5', '18'])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.47/0.68      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.47/0.68  thf(t98_xboole_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      (![X13 : $i, X14 : $i]:
% 0.47/0.68         ((k2_xboole_0 @ X13 @ X14)
% 0.47/0.68           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.47/0.68  thf(t42_enumset1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.47/0.68       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.68         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.47/0.68           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k2_tarski @ X18 @ X19)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.47/0.68      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.47/0.68  thf('24', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['0', '23'])).
% 0.47/0.68  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
