%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ESXFpowGCc

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:38 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  395 ( 395 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t74_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ),
    inference('cnf.neg',[status(esa)],[t74_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k2_tarski @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X6 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ESXFpowGCc
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 145 iterations in 0.093s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.36/0.53                                           $i > $i).
% 0.36/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.53  thf(t74_enumset1, conjecture,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.53     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.53       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.53        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.53          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t74_enumset1])).
% 0.36/0.53  thf('0', plain,
% 0.36/0.53      (((k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.36/0.53         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t72_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.36/0.53         ((k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38)
% 0.36/0.53           = (k2_enumset1 @ X35 @ X36 @ X37 @ X38))),
% 0.36/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.53  thf(t73_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.53     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.36/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.36/0.53  thf('2', plain,
% 0.36/0.53      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.53         ((k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.36/0.53           = (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.36/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.36/0.53  thf(t67_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.53     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.53       ( k2_xboole_0 @
% 0.36/0.53         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 0.36/0.53         X28 : $i]:
% 0.36/0.53         ((k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.36/0.53           = (k2_xboole_0 @ 
% 0.36/0.53              (k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 0.36/0.53              (k2_tarski @ X27 @ X28)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.53         ((k6_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 0.36/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.36/0.53              (k2_tarski @ X6 @ X5)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.53  thf(t69_enumset1, axiom,
% 0.36/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.53  thf('5', plain, (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.36/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.53  thf(t63_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.53     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.53       ( k2_xboole_0 @
% 0.36/0.53         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.36/0.53  thf('6', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.36/0.53         X20 : $i]:
% 0.36/0.53         ((k6_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.36/0.53           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ 
% 0.36/0.53              (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.53         ((k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)
% 0.36/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.36/0.53              (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.53  thf(t56_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.36/0.53     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.36/0.53       ( k2_xboole_0 @
% 0.36/0.53         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.53         ((k5_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.36/0.53           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.36/0.53              (k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.53         ((k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1)
% 0.36/0.53           = (k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1))),
% 0.36/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.53         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5)
% 0.36/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.36/0.53              (k2_tarski @ X6 @ X5)))),
% 0.36/0.53      inference('demod', [status(thm)], ['4', '9'])).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.53         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.36/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.36/0.53              (k2_tarski @ X5 @ X4)))),
% 0.36/0.53      inference('sup+', [status(thm)], ['1', '10'])).
% 0.36/0.53  thf(t54_enumset1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.53     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.53       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.36/0.53  thf('12', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.53         ((k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5)
% 0.36/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.36/0.53              (k2_tarski @ X4 @ X5)))),
% 0.36/0.53      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.36/0.53  thf('13', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.53         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.36/0.53           = (k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4))),
% 0.36/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.53  thf('14', plain,
% 0.36/0.53      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.36/0.53         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.36/0.53      inference('demod', [status(thm)], ['0', '13'])).
% 0.36/0.53  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
