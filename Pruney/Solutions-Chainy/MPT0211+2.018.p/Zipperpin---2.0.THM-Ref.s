%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.brbbSOqAsw

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:32 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  307 ( 338 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X49: $i,X50: $i] :
      ( ( k1_enumset1 @ X49 @ X49 @ X50 )
      = ( k2_tarski @ X49 @ X50 ) ) ),
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
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 )
      = ( k2_enumset1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X19 @ X22 @ X20 @ X21 )
      = ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('7',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X34 @ X33 @ X32 @ X31 )
      = ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X52 @ X53 )
      = ( k1_enumset1 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X26 @ X25 @ X24 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('12',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X52 @ X53 )
      = ( k1_enumset1 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X19 @ X22 @ X20 @ X21 )
      = ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('15',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X52 @ X53 )
      = ( k1_enumset1 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','10','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.brbbSOqAsw
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 83 iterations in 0.082s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(t137_enumset1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.37/0.54       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.54        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.37/0.54          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.37/0.54         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t70_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X49 : $i, X50 : $i]:
% 0.37/0.54         ((k1_enumset1 @ X49 @ X49 @ X50) = (k2_tarski @ X49 @ X50))),
% 0.37/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.54  thf(l57_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.54     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.37/0.54       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.54         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.37/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.37/0.54              (k2_tarski @ X9 @ X10)))),
% 0.37/0.54      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.37/0.54           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (((k3_enumset1 @ sk_B @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.37/0.54         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.54  thf(t72_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.37/0.54         ((k3_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57)
% 0.37/0.54           = (k2_enumset1 @ X54 @ X55 @ X56 @ X57))),
% 0.37/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.37/0.54  thf(t105_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X19 @ X22 @ X20 @ X21)
% 0.37/0.54           = (k2_enumset1 @ X19 @ X20 @ X21 @ X22))),
% 0.37/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 0.37/0.54         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.37/0.54  thf(t125_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X34 @ X33 @ X32 @ X31)
% 0.37/0.54           = (k2_enumset1 @ X31 @ X32 @ X33 @ X34))),
% 0.37/0.54      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.37/0.54  thf(t71_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X51 @ X51 @ X52 @ X53)
% 0.37/0.54           = (k1_enumset1 @ X51 @ X52 @ X53))),
% 0.37/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.37/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.54  thf(t107_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X23 @ X26 @ X25 @ X24)
% 0.37/0.54           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.37/0.54      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X51 @ X51 @ X52 @ X53)
% 0.37/0.54           = (k1_enumset1 @ X51 @ X52 @ X53))),
% 0.37/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.37/0.54      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X19 @ X22 @ X20 @ X21)
% 0.37/0.54           = (k2_enumset1 @ X19 @ X20 @ X21 @ X22))),
% 0.37/0.54      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X51 @ X51 @ X52 @ X53)
% 0.37/0.54           = (k1_enumset1 @ X51 @ X52 @ X53))),
% 0.37/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.37/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.37/0.54      inference('sup+', [status(thm)], ['13', '16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.37/0.54         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.54      inference('demod', [status(thm)], ['7', '10', '17'])).
% 0.37/0.54  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
