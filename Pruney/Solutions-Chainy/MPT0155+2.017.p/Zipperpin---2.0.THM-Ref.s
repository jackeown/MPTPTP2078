%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CtkjsxOR4M

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:28 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  534 ( 661 expanded)
%              Number of equality atoms :   46 (  59 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf(t52_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t52_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18','27'])).

thf('29',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CtkjsxOR4M
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 281 iterations in 0.161s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.37/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.62  thf(t71_enumset1, conjecture,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.62        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.37/0.62  thf('0', plain,
% 0.37/0.62      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.37/0.62         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(t69_enumset1, axiom,
% 0.37/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.62  thf('1', plain, (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.37/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.62  thf(t70_enumset1, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      (![X40 : $i, X41 : $i]:
% 0.37/0.62         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.37/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.62  thf(t44_enumset1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.37/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.37/0.62           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['1', '4'])).
% 0.37/0.62  thf('6', plain, (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.37/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.62  thf(t43_enumset1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.37/0.62       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.62         ((k1_enumset1 @ X13 @ X14 @ X15)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X15)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('9', plain,
% 0.37/0.62      (![X40 : $i, X41 : $i]:
% 0.37/0.62         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.37/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_tarski @ X0 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.37/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf(t52_enumset1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.62     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.37/0.62       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ))).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.62         ((k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X25 @ X26) @ 
% 0.37/0.62              (k2_enumset1 @ X27 @ X28 @ X29 @ X30)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t52_enumset1])).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X40 : $i, X41 : $i]:
% 0.37/0.62         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.37/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.62  thf(l62_enumset1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.62     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.37/0.62       ( k2_xboole_0 @
% 0.37/0.62         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.62         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.37/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.37/0.62              (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.37/0.62      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.62         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.37/0.62              (k2_tarski @ X1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.62  thf(l57_enumset1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.62     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.37/0.62       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.37/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.37/0.62              (k2_tarski @ X5 @ X6)))),
% 0.37/0.62      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.62         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.37/0.62           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X40 : $i, X41 : $i]:
% 0.37/0.62         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.37/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.37/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.37/0.62              (k2_tarski @ X5 @ X6)))),
% 0.37/0.62      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.37/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.62  thf(t48_enumset1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.62     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.37/0.62       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ 
% 0.37/0.62              (k1_enumset1 @ X22 @ X23 @ X24)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.37/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.62         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.37/0.62           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_enumset1 @ X17 @ X18 @ X19)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.37/0.62           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.37/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.37/0.62           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['21', '26'])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 0.37/0.62           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['13', '18', '27'])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.37/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.62         ((k1_enumset1 @ X13 @ X14 @ X15)
% 0.37/0.62           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X15)))),
% 0.37/0.62      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.37/0.62      inference('sup+', [status(thm)], ['28', '33'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.37/0.62         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.62      inference('demod', [status(thm)], ['0', '34'])).
% 0.37/0.62  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
