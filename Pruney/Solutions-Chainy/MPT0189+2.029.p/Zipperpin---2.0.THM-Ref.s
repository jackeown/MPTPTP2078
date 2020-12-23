%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pN5bkRw39U

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:10 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   41 (  62 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  377 ( 671 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X4 @ X5 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_enumset1 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X45 @ X45 @ X46 @ X47 )
      = ( k1_enumset1 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 )
      = ( k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('9',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k5_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k4_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('10',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 )
      = ( k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_enumset1 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X9 @ X8 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('19',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','17','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pN5bkRw39U
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.33/2.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.57  % Solved by: fo/fo7.sh
% 2.33/2.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.57  % done 2730 iterations in 2.108s
% 2.33/2.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.57  % SZS output start Refutation
% 2.33/2.57  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.33/2.57  thf(sk_D_type, type, sk_D: $i).
% 2.33/2.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.33/2.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.33/2.57  thf(sk_B_type, type, sk_B: $i).
% 2.33/2.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.33/2.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 2.33/2.57  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 2.33/2.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.33/2.57  thf(sk_C_type, type, sk_C: $i).
% 2.33/2.57  thf(t108_enumset1, conjecture,
% 2.33/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 2.33/2.57  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.57        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 2.33/2.57    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 2.33/2.57  thf('0', plain,
% 2.33/2.57      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.33/2.57         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 2.33/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.57  thf(t100_enumset1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i]:
% 2.33/2.57     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 2.33/2.57  thf('1', plain,
% 2.33/2.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.33/2.57         ((k1_enumset1 @ X6 @ X4 @ X5) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 2.33/2.57      inference('cnf', [status(esa)], [t100_enumset1])).
% 2.33/2.57  thf(t72_enumset1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.33/2.57  thf('2', plain,
% 2.33/2.57      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.33/2.57         ((k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51)
% 2.33/2.57           = (k2_enumset1 @ X48 @ X49 @ X50 @ X51))),
% 2.33/2.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.33/2.57  thf(t71_enumset1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i]:
% 2.33/2.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.33/2.57  thf('3', plain,
% 2.33/2.57      (![X45 : $i, X46 : $i, X47 : $i]:
% 2.33/2.57         ((k2_enumset1 @ X45 @ X45 @ X46 @ X47)
% 2.33/2.57           = (k1_enumset1 @ X45 @ X46 @ X47))),
% 2.33/2.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.33/2.57  thf('4', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.57         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.33/2.57      inference('sup+', [status(thm)], ['2', '3'])).
% 2.33/2.57  thf(t73_enumset1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.33/2.57     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 2.33/2.57       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 2.33/2.57  thf('5', plain,
% 2.33/2.57      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 2.33/2.57         ((k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56)
% 2.33/2.57           = (k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56))),
% 2.33/2.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.33/2.57  thf(t61_enumset1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 2.33/2.57     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 2.33/2.57       ( k2_xboole_0 @
% 2.33/2.57         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 2.33/2.57  thf('6', plain,
% 2.33/2.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.33/2.57         ((k5_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 2.33/2.57           = (k2_xboole_0 @ 
% 2.33/2.57              (k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16) @ 
% 2.33/2.57              (k1_tarski @ X17)))),
% 2.33/2.57      inference('cnf', [status(esa)], [t61_enumset1])).
% 2.33/2.57  thf('7', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.33/2.57         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 2.33/2.57           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 2.33/2.57              (k1_tarski @ X5)))),
% 2.33/2.57      inference('sup+', [status(thm)], ['5', '6'])).
% 2.33/2.57  thf('8', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.33/2.57         ((k5_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3)
% 2.33/2.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 2.33/2.57      inference('sup+', [status(thm)], ['4', '7'])).
% 2.33/2.57  thf(t74_enumset1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.33/2.57     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 2.33/2.57       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 2.33/2.57  thf('9', plain,
% 2.33/2.57      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 2.33/2.57         ((k5_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62)
% 2.33/2.57           = (k4_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 2.33/2.57      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.33/2.57  thf('10', plain,
% 2.33/2.57      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 2.33/2.57         ((k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56)
% 2.33/2.57           = (k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56))),
% 2.33/2.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.33/2.57  thf('11', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.33/2.57         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 2.33/2.57           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.33/2.57      inference('sup+', [status(thm)], ['9', '10'])).
% 2.33/2.57  thf('12', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.33/2.57         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 2.33/2.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 2.33/2.57      inference('demod', [status(thm)], ['8', '11'])).
% 2.33/2.57  thf('13', plain,
% 2.33/2.57      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.33/2.57         ((k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51)
% 2.33/2.57           = (k2_enumset1 @ X48 @ X49 @ X50 @ X51))),
% 2.33/2.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.33/2.57  thf('14', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.33/2.57         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 2.33/2.57           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.33/2.57      inference('sup+', [status(thm)], ['12', '13'])).
% 2.33/2.57  thf('15', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.33/2.57         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 2.33/2.57           = (k2_enumset1 @ X1 @ X0 @ X2 @ X3))),
% 2.33/2.57      inference('sup+', [status(thm)], ['1', '14'])).
% 2.33/2.57  thf('16', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.33/2.57         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 2.33/2.57           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.33/2.57      inference('sup+', [status(thm)], ['12', '13'])).
% 2.33/2.57  thf('17', plain,
% 2.33/2.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.33/2.57         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 2.33/2.57      inference('sup+', [status(thm)], ['15', '16'])).
% 2.33/2.57  thf(t104_enumset1, axiom,
% 2.33/2.57    (![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.57     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 2.33/2.57  thf('18', plain,
% 2.33/2.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 2.33/2.57         ((k2_enumset1 @ X7 @ X9 @ X8 @ X10)
% 2.33/2.57           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 2.33/2.57      inference('cnf', [status(esa)], [t104_enumset1])).
% 2.33/2.57  thf('19', plain,
% 2.33/2.57      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.33/2.57         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 2.33/2.57      inference('demod', [status(thm)], ['0', '17', '18'])).
% 2.33/2.57  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 2.33/2.57  
% 2.33/2.57  % SZS output end Refutation
% 2.33/2.57  
% 2.33/2.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
