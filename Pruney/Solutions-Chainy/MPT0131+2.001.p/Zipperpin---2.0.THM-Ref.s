%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Jq7eYmgkQ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:57 EST 2020

% Result     : Theorem 18.37s
% Output     : Refutation 18.37s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  425 ( 591 expanded)
%              Number of equality atoms :   34 (  50 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t47_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k3_enumset1 @ A @ B @ C @ D @ E )
        = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_C @ sk_D @ sk_E @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ X3 @ ( k1_tarski @ X2 ) ) )
      = ( k2_xboole_0 @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_enumset1 @ X0 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['10','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Jq7eYmgkQ
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.37/18.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.37/18.55  % Solved by: fo/fo7.sh
% 18.37/18.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.37/18.55  % done 4857 iterations in 18.092s
% 18.37/18.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.37/18.55  % SZS output start Refutation
% 18.37/18.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 18.37/18.55  thf(sk_E_type, type, sk_E: $i).
% 18.37/18.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 18.37/18.55  thf(sk_A_type, type, sk_A: $i).
% 18.37/18.55  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 18.37/18.55  thf(sk_C_type, type, sk_C: $i).
% 18.37/18.55  thf(sk_D_type, type, sk_D: $i).
% 18.37/18.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 18.37/18.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.37/18.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 18.37/18.55  thf(sk_B_type, type, sk_B: $i).
% 18.37/18.55  thf(t47_enumset1, conjecture,
% 18.37/18.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 18.37/18.55     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 18.37/18.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 18.37/18.55  thf(zf_stmt_0, negated_conjecture,
% 18.37/18.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 18.37/18.55        ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 18.37/18.55          ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )),
% 18.37/18.55    inference('cnf.neg', [status(esa)], [t47_enumset1])).
% 18.37/18.55  thf('0', plain,
% 18.37/18.55      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 18.37/18.55         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 18.37/18.55             (k2_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 18.37/18.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.37/18.55  thf(t44_enumset1, axiom,
% 18.37/18.55    (![A:$i,B:$i,C:$i,D:$i]:
% 18.37/18.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 18.37/18.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 18.37/18.55  thf('1', plain,
% 18.37/18.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 18.37/18.55         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_enumset1 @ X16 @ X17 @ X18)))),
% 18.37/18.55      inference('cnf', [status(esa)], [t44_enumset1])).
% 18.37/18.55  thf(t41_enumset1, axiom,
% 18.37/18.55    (![A:$i,B:$i]:
% 18.37/18.55     ( ( k2_tarski @ A @ B ) =
% 18.37/18.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 18.37/18.55  thf('2', plain,
% 18.37/18.55      (![X10 : $i, X11 : $i]:
% 18.37/18.55         ((k2_tarski @ X10 @ X11)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 18.37/18.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 18.37/18.55  thf(t4_xboole_1, axiom,
% 18.37/18.55    (![A:$i,B:$i,C:$i]:
% 18.37/18.55     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 18.37/18.55       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 18.37/18.55  thf('3', plain,
% 18.37/18.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 18.37/18.55           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 18.37/18.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 18.37/18.55  thf('4', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 18.37/18.55              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 18.37/18.55      inference('sup+', [status(thm)], ['2', '3'])).
% 18.37/18.55  thf('5', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 18.37/18.55              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 18.37/18.55      inference('sup+', [status(thm)], ['1', '4'])).
% 18.37/18.55  thf(l57_enumset1, axiom,
% 18.37/18.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 18.37/18.55     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 18.37/18.55       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 18.37/18.55  thf('6', plain,
% 18.37/18.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 18.37/18.55         ((k3_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9)
% 18.37/18.55           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X6 @ X7) @ 
% 18.37/18.55              (k2_tarski @ X8 @ X9)))),
% 18.37/18.55      inference('cnf', [status(esa)], [l57_enumset1])).
% 18.37/18.55  thf(commutativity_k2_xboole_0, axiom,
% 18.37/18.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 18.37/18.55  thf('7', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.37/18.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.37/18.55  thf('8', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_enumset1 @ X4 @ X3 @ X2))
% 18.37/18.55           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 18.37/18.55      inference('sup+', [status(thm)], ['6', '7'])).
% 18.37/18.55  thf('9', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 18.37/18.55              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 18.37/18.55      inference('demod', [status(thm)], ['5', '8'])).
% 18.37/18.55  thf('10', plain,
% 18.37/18.55      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 18.37/18.55         != (k3_enumset1 @ sk_C @ sk_D @ sk_E @ sk_A @ sk_B))),
% 18.37/18.55      inference('demod', [status(thm)], ['0', '9'])).
% 18.37/18.55  thf('11', plain,
% 18.37/18.55      (![X10 : $i, X11 : $i]:
% 18.37/18.55         ((k2_tarski @ X10 @ X11)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X11)))),
% 18.37/18.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 18.37/18.55  thf('12', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 18.37/18.55              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 18.37/18.55      inference('sup+', [status(thm)], ['2', '3'])).
% 18.37/18.55  thf('13', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 18.37/18.55      inference('sup+', [status(thm)], ['11', '12'])).
% 18.37/18.55  thf(t42_enumset1, axiom,
% 18.37/18.55    (![A:$i,B:$i,C:$i]:
% 18.37/18.55     ( ( k1_enumset1 @ A @ B @ C ) =
% 18.37/18.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 18.37/18.55  thf('14', plain,
% 18.37/18.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 18.37/18.55         ((k1_enumset1 @ X12 @ X13 @ X14)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k2_tarski @ X13 @ X14)))),
% 18.37/18.55      inference('cnf', [status(esa)], [t42_enumset1])).
% 18.37/18.55  thf('15', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 18.37/18.55           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 18.37/18.55      inference('demod', [status(thm)], ['13', '14'])).
% 18.37/18.55  thf('16', plain,
% 18.37/18.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 18.37/18.55         ((k1_enumset1 @ X12 @ X13 @ X14)
% 18.37/18.55           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k2_tarski @ X13 @ X14)))),
% 18.37/18.55      inference('cnf', [status(esa)], [t42_enumset1])).
% 18.37/18.55  thf('17', plain,
% 18.37/18.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 18.37/18.55           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 18.37/18.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 18.37/18.55  thf('18', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.37/18.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.37/18.55  thf('19', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 18.37/18.55           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.37/18.55      inference('sup+', [status(thm)], ['17', '18'])).
% 18.37/18.55  thf('20', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 18.37/18.55           (k2_xboole_0 @ X3 @ (k1_tarski @ X2)))
% 18.37/18.55           = (k2_xboole_0 @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 18.37/18.55      inference('sup+', [status(thm)], ['16', '19'])).
% 18.37/18.55  thf('21', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 18.37/18.55           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 18.37/18.55              (k1_enumset1 @ X0 @ X4 @ X3)))),
% 18.37/18.55      inference('sup+', [status(thm)], ['15', '20'])).
% 18.37/18.55  thf('22', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_enumset1 @ X4 @ X3 @ X2))
% 18.37/18.55           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 18.37/18.55      inference('sup+', [status(thm)], ['6', '7'])).
% 18.37/18.55  thf('23', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_enumset1 @ X4 @ X3 @ X2))
% 18.37/18.55           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 18.37/18.55      inference('sup+', [status(thm)], ['6', '7'])).
% 18.37/18.55  thf('24', plain,
% 18.37/18.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.37/18.55         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 18.37/18.55           = (k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 18.37/18.55      inference('demod', [status(thm)], ['21', '22', '23'])).
% 18.37/18.55  thf('25', plain,
% 18.37/18.55      (((k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 18.37/18.55         != (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))),
% 18.37/18.55      inference('demod', [status(thm)], ['10', '24'])).
% 18.37/18.55  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 18.37/18.55  
% 18.37/18.55  % SZS output end Refutation
% 18.37/18.55  
% 18.37/18.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
