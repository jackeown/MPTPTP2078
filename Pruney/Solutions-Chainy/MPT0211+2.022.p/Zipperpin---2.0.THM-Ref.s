%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.73AXtHyd4f

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:33 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  52 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  443 ( 485 expanded)
%              Number of equality atoms :   37 (  41 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X17 @ X14 @ X16 @ X15 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('9',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) @ ( k2_tarski @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('13',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ( k5_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 )
      = ( k4_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X2 ) @ ( k2_tarski @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ ( k2_tarski @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('19',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('22',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','17','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.73AXtHyd4f
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.16/4.38  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.16/4.38  % Solved by: fo/fo7.sh
% 4.16/4.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.16/4.38  % done 4459 iterations in 3.923s
% 4.16/4.38  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.16/4.38  % SZS output start Refutation
% 4.16/4.38  thf(sk_A_type, type, sk_A: $i).
% 4.16/4.38  thf(sk_B_type, type, sk_B: $i).
% 4.16/4.38  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 4.16/4.38  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.16/4.38  thf(sk_C_type, type, sk_C: $i).
% 4.16/4.38  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.16/4.38  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.16/4.38  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 4.16/4.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.16/4.38  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.16/4.38  thf(t137_enumset1, conjecture,
% 4.16/4.38    (![A:$i,B:$i,C:$i]:
% 4.16/4.38     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 4.16/4.38       ( k1_enumset1 @ A @ B @ C ) ))).
% 4.16/4.38  thf(zf_stmt_0, negated_conjecture,
% 4.16/4.38    (~( ![A:$i,B:$i,C:$i]:
% 4.16/4.38        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 4.16/4.38          ( k1_enumset1 @ A @ B @ C ) ) )),
% 4.16/4.38    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 4.16/4.38  thf('0', plain,
% 4.16/4.38      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 4.16/4.38         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 4.16/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.38  thf(t113_enumset1, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.16/4.38     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 4.16/4.38  thf('1', plain,
% 4.16/4.38      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 4.16/4.38         ((k2_enumset1 @ X17 @ X14 @ X16 @ X15)
% 4.16/4.38           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 4.16/4.38      inference('cnf', [status(esa)], [t113_enumset1])).
% 4.16/4.38  thf(t71_enumset1, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i]:
% 4.16/4.38     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.16/4.38  thf('2', plain,
% 4.16/4.38      (![X48 : $i, X49 : $i, X50 : $i]:
% 4.16/4.38         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 4.16/4.38           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 4.16/4.38      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.16/4.38  thf('3', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 4.16/4.38      inference('sup+', [status(thm)], ['1', '2'])).
% 4.16/4.38  thf(t72_enumset1, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.16/4.38     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.16/4.38  thf('4', plain,
% 4.16/4.38      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 4.16/4.38         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 4.16/4.38           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 4.16/4.38      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.16/4.38  thf('5', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.16/4.38      inference('sup+', [status(thm)], ['3', '4'])).
% 4.16/4.38  thf(t73_enumset1, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.16/4.38     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 4.16/4.38       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 4.16/4.38  thf('6', plain,
% 4.16/4.38      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 4.16/4.38         ((k4_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59)
% 4.16/4.38           = (k3_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 4.16/4.38      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.16/4.38  thf('7', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((k4_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 @ X2)
% 4.16/4.38           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.16/4.38      inference('sup+', [status(thm)], ['5', '6'])).
% 4.16/4.38  thf('8', plain,
% 4.16/4.38      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 4.16/4.38         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 4.16/4.38           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 4.16/4.38      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.16/4.38  thf('9', plain,
% 4.16/4.38      (![X48 : $i, X49 : $i, X50 : $i]:
% 4.16/4.38         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 4.16/4.38           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 4.16/4.38      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.16/4.38  thf('10', plain,
% 4.16/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.38         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.16/4.38      inference('sup+', [status(thm)], ['8', '9'])).
% 4.16/4.38  thf(t60_enumset1, axiom,
% 4.16/4.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 4.20/4.38     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 4.20/4.38       ( k2_xboole_0 @
% 4.20/4.38         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 4.20/4.38  thf('11', plain,
% 4.20/4.38      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 4.20/4.38         ((k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 4.20/4.38           = (k2_xboole_0 @ (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35) @ 
% 4.20/4.38              (k2_tarski @ X36 @ X37)))),
% 4.20/4.38      inference('cnf', [status(esa)], [t60_enumset1])).
% 4.20/4.38  thf('12', plain,
% 4.20/4.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.20/4.38         ((k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 4.20/4.38           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 4.20/4.38              (k2_tarski @ X4 @ X3)))),
% 4.20/4.38      inference('sup+', [status(thm)], ['10', '11'])).
% 4.20/4.38  thf(t74_enumset1, axiom,
% 4.20/4.38    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.20/4.38     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 4.20/4.38       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 4.20/4.38  thf('13', plain,
% 4.20/4.38      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 4.20/4.38         ((k5_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65)
% 4.20/4.38           = (k4_enumset1 @ X60 @ X61 @ X62 @ X63 @ X64 @ X65))),
% 4.20/4.38      inference('cnf', [status(esa)], [t74_enumset1])).
% 4.20/4.38  thf('14', plain,
% 4.20/4.38      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.20/4.38         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 4.20/4.38           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 4.20/4.38              (k2_tarski @ X4 @ X3)))),
% 4.20/4.38      inference('demod', [status(thm)], ['12', '13'])).
% 4.20/4.38  thf('15', plain,
% 4.20/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.20/4.38         ((k1_enumset1 @ X2 @ X1 @ X0)
% 4.20/4.38           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X2) @ 
% 4.20/4.38              (k2_tarski @ X1 @ X2)))),
% 4.20/4.38      inference('sup+', [status(thm)], ['7', '14'])).
% 4.20/4.38  thf(t70_enumset1, axiom,
% 4.20/4.38    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.20/4.38  thf('16', plain,
% 4.20/4.38      (![X46 : $i, X47 : $i]:
% 4.20/4.38         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 4.20/4.38      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.20/4.38  thf('17', plain,
% 4.20/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.20/4.38         ((k1_enumset1 @ X2 @ X1 @ X0)
% 4.20/4.38           = (k2_xboole_0 @ (k2_tarski @ X0 @ X2) @ (k2_tarski @ X1 @ X2)))),
% 4.20/4.38      inference('demod', [status(thm)], ['15', '16'])).
% 4.20/4.38  thf(t107_enumset1, axiom,
% 4.20/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.20/4.38     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 4.20/4.38  thf('18', plain,
% 4.20/4.38      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 4.20/4.38         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 4.20/4.38           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 4.20/4.38      inference('cnf', [status(esa)], [t107_enumset1])).
% 4.20/4.38  thf('19', plain,
% 4.20/4.38      (![X48 : $i, X49 : $i, X50 : $i]:
% 4.20/4.38         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 4.20/4.38           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 4.20/4.38      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.20/4.38  thf('20', plain,
% 4.20/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.20/4.38         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 4.20/4.38      inference('sup+', [status(thm)], ['18', '19'])).
% 4.20/4.38  thf(t105_enumset1, axiom,
% 4.20/4.38    (![A:$i,B:$i,C:$i,D:$i]:
% 4.20/4.38     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 4.20/4.38  thf('21', plain,
% 4.20/4.38      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 4.20/4.38         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 4.20/4.38      inference('cnf', [status(esa)], [t105_enumset1])).
% 4.20/4.38  thf('22', plain,
% 4.20/4.38      (![X48 : $i, X49 : $i, X50 : $i]:
% 4.20/4.38         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 4.20/4.38           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 4.20/4.38      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.20/4.38  thf('23', plain,
% 4.20/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.20/4.38         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 4.20/4.38      inference('sup+', [status(thm)], ['21', '22'])).
% 4.20/4.38  thf('24', plain,
% 4.20/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.20/4.38         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 4.20/4.38      inference('sup+', [status(thm)], ['20', '23'])).
% 4.20/4.38  thf('25', plain,
% 4.20/4.38      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 4.20/4.38         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 4.20/4.38      inference('demod', [status(thm)], ['0', '17', '24'])).
% 4.20/4.38  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 4.20/4.38  
% 4.20/4.38  % SZS output end Refutation
% 4.20/4.38  
% 4.20/4.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
