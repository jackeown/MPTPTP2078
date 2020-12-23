%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qgFPvy15Aw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:32 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  316 ( 379 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k3_enumset1 @ sk_B @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X13 @ X12 @ X14 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X26 @ X25 @ X24 @ X23 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ( k1_enumset1 @ sk_A @ sk_C @ sk_B )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X13 @ X12 @ X14 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('13',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X18 @ X17 @ X16 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qgFPvy15Aw
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.71  % Solved by: fo/fo7.sh
% 0.49/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.71  % done 335 iterations in 0.271s
% 0.49/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.71  % SZS output start Refutation
% 0.49/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.49/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.49/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.49/0.71  thf(t137_enumset1, conjecture,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.49/0.71       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.49/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.71        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.49/0.71          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.49/0.71    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.49/0.71  thf('0', plain,
% 0.49/0.71      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.49/0.71         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(t70_enumset1, axiom,
% 0.49/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.49/0.71  thf('1', plain,
% 0.49/0.71      (![X40 : $i, X41 : $i]:
% 0.49/0.71         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.49/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.49/0.71  thf(l57_enumset1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.49/0.71     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.49/0.71       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.49/0.71  thf('2', plain,
% 0.49/0.71      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.71         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.49/0.71           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.49/0.71              (k2_tarski @ X9 @ X10)))),
% 0.49/0.71      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.49/0.71  thf('3', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.71         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.49/0.71           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.49/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.49/0.71  thf('4', plain,
% 0.49/0.71      (((k3_enumset1 @ sk_B @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.49/0.71         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.71  thf(t72_enumset1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.49/0.71  thf('5', plain,
% 0.49/0.71      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.49/0.71         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 0.49/0.71           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 0.49/0.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.49/0.71  thf(t104_enumset1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.49/0.71  thf('6', plain,
% 0.49/0.71      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X11 @ X13 @ X12 @ X14)
% 0.49/0.71           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.49/0.71      inference('cnf', [status(esa)], [t104_enumset1])).
% 0.49/0.71  thf('7', plain,
% 0.49/0.71      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 0.49/0.71         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.49/0.71  thf(t125_enumset1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.49/0.71  thf('8', plain,
% 0.49/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X26 @ X25 @ X24 @ X23)
% 0.49/0.71           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.49/0.71      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.49/0.71  thf(t71_enumset1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.49/0.71  thf('9', plain,
% 0.49/0.71      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.49/0.71           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.49/0.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.49/0.71  thf('10', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.49/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.49/0.71  thf('11', plain,
% 0.49/0.71      (((k1_enumset1 @ sk_A @ sk_C @ sk_B)
% 0.49/0.71         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['7', '10'])).
% 0.49/0.71  thf('12', plain,
% 0.49/0.71      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X11 @ X13 @ X12 @ X14)
% 0.49/0.71           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.49/0.71      inference('cnf', [status(esa)], [t104_enumset1])).
% 0.49/0.71  thf('13', plain,
% 0.49/0.71      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 0.49/0.71           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 0.49/0.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.49/0.71  thf('14', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.49/0.71      inference('sup+', [status(thm)], ['12', '13'])).
% 0.49/0.71  thf(t107_enumset1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.49/0.71  thf('15', plain,
% 0.49/0.71      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X15 @ X18 @ X17 @ X16)
% 0.49/0.71           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.49/0.71      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.49/0.71  thf('16', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X2 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.49/0.71      inference('sup+', [status(thm)], ['14', '15'])).
% 0.49/0.71  thf('17', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.49/0.71      inference('sup+', [status(thm)], ['12', '13'])).
% 0.49/0.71  thf('18', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.71         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.49/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.49/0.71  thf('19', plain,
% 0.49/0.71      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.49/0.71         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['11', '18'])).
% 0.49/0.71  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.49/0.71  
% 0.49/0.71  % SZS output end Refutation
% 0.49/0.71  
% 0.49/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
