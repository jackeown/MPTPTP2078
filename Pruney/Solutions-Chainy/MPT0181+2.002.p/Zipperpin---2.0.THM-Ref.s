%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9FFpAAqme4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:57 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  418 ( 539 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   16 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5 )
      = ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 ) ) ),
    inference(demod,[status(thm)],['5','6','11'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9FFpAAqme4
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 145 iterations in 0.072s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.34/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(t98_enumset1, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.53        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t98_enumset1])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.34/0.53         != (k1_enumset1 @ sk_A @ sk_C @ sk_B))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t72_enumset1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.53         ((k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21)
% 0.34/0.53           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 0.34/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.34/0.53  thf(commutativity_k2_tarski, axiom,
% 0.34/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.34/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.34/0.53  thf(t60_enumset1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.34/0.53     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.34/0.53       ( k2_xboole_0 @
% 0.34/0.53         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.34/0.53         ((k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.34/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 0.34/0.53              (k2_tarski @ X11 @ X12)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.53         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.34/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.34/0.53              (k2_tarski @ X1 @ X0)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.53         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5)
% 0.34/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.34/0.53              (k2_tarski @ X5 @ X4)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['1', '4'])).
% 0.34/0.53  thf(t74_enumset1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.34/0.53     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.34/0.53       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.34/0.53         ((k5_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.34/0.53           = (k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 0.34/0.53      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.53         ((k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21)
% 0.34/0.53           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 0.34/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.34/0.53         ((k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.34/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 0.34/0.53              (k2_tarski @ X11 @ X12)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.53         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.34/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.34/0.53              (k2_tarski @ X5 @ X4)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.34/0.53         ((k5_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.34/0.53           = (k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 0.34/0.53      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.53         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.34/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.34/0.53              (k2_tarski @ X5 @ X4)))),
% 0.34/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.53         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 @ X5)
% 0.34/0.53           = (k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4))),
% 0.34/0.53      inference('demod', [status(thm)], ['5', '6', '11'])).
% 0.34/0.53  thf(t73_enumset1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.34/0.53     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.34/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.34/0.53         ((k4_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.34/0.53           = (k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26))),
% 0.34/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.34/0.53         ((k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21)
% 0.34/0.53           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 0.34/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.34/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.34/0.53           = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['12', '15'])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.34/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf(t71_enumset1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.34/0.53         ((k2_enumset1 @ X15 @ X15 @ X16 @ X17)
% 0.34/0.53           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.34/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.34/0.53         ((k2_enumset1 @ X15 @ X15 @ X16 @ X17)
% 0.34/0.53           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.34/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.34/0.53         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.34/0.53      inference('demod', [status(thm)], ['0', '22'])).
% 0.34/0.53  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.34/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
