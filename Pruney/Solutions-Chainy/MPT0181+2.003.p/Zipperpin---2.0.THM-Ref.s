%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sfMtsADJoI

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  436 ( 592 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t98_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ A @ C @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t98_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('6',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k6_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k5_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k5_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X16 @ X16 @ X17 @ X18 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X16 @ X16 @ X17 @ X18 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sfMtsADJoI
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 126 iterations in 0.092s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.54                                           $i > $i).
% 0.20/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(t98_enumset1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t98_enumset1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54         != (k1_enumset1 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(commutativity_k2_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.54  thf(t67_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.54     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.54       ( k2_xboole_0 @
% 0.20/0.54         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.20/0.54         X13 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.54           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11) @ 
% 0.20/0.54              (k2_tarski @ X12 @ X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.20/0.54           = (k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.54              (k2_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.20/0.54         X13 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.54           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11) @ 
% 0.20/0.54              (k2_tarski @ X12 @ X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.20/0.54           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf(t75_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.54     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.54       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.20/0.54           = (k5_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40))),
% 0.20/0.54      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.20/0.54  thf(t74_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.54     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.54       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.54         ((k5_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.20/0.54           = (k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.20/0.54      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf(t73_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.54       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.54         ((k4_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.20/0.54           = (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['5', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf(t72_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22)
% 0.20/0.54           = (k2_enumset1 @ X19 @ X20 @ X21 @ X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22)
% 0.20/0.54           = (k2_enumset1 @ X19 @ X20 @ X21 @ X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf(t71_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X16 @ X16 @ X17 @ X18)
% 0.20/0.54           = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X16 @ X16 @ X17 @ X18)
% 0.20/0.54           = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.54         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '21'])).
% 0.20/0.54  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
