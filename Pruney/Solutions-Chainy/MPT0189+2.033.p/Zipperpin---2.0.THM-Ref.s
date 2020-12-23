%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AOp6iRsXRj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:10 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  320 ( 533 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X23 @ X23 @ X24 @ X25 )
      = ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','9','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AOp6iRsXRj
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:39:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.73/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.73/0.91  % Solved by: fo/fo7.sh
% 0.73/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.91  % done 1291 iterations in 0.475s
% 0.73/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.73/0.91  % SZS output start Refutation
% 0.73/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.73/0.91  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.73/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.73/0.91  thf(sk_D_type, type, sk_D: $i).
% 0.73/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.73/0.91  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.73/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.73/0.91  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.73/0.91  thf(t108_enumset1, conjecture,
% 0.73/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.91     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.73/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.91        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.73/0.91    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.73/0.91  thf('0', plain,
% 0.73/0.91      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.73/0.91         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.73/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.91  thf(t100_enumset1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.73/0.91  thf('1', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.91         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.73/0.91      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.73/0.91  thf(t71_enumset1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i]:
% 0.73/0.91     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.73/0.91  thf('2', plain,
% 0.73/0.91      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.73/0.91         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.73/0.91           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.73/0.91      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.73/0.91  thf(t50_enumset1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.73/0.91     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.73/0.91       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.73/0.91  thf('3', plain,
% 0.73/0.91      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.73/0.91         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.73/0.91           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.73/0.91              (k1_tarski @ X11)))),
% 0.73/0.91      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.73/0.91  thf('4', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.73/0.91           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.73/0.91      inference('sup+', [status(thm)], ['2', '3'])).
% 0.73/0.91  thf(t72_enumset1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.91     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.73/0.91  thf('5', plain,
% 0.73/0.91      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.73/0.91         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 0.73/0.91           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.73/0.91      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.73/0.91  thf('6', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.73/0.91           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.73/0.91      inference('sup+', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('7', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.73/0.91           = (k2_enumset1 @ X1 @ X0 @ X2 @ X3))),
% 0.73/0.91      inference('sup+', [status(thm)], ['1', '6'])).
% 0.73/0.91  thf('8', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.73/0.91           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.73/0.91      inference('sup+', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('9', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X3 @ X2 @ X0))),
% 0.73/0.91      inference('sup+', [status(thm)], ['7', '8'])).
% 0.73/0.91  thf(t103_enumset1, axiom,
% 0.73/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.73/0.91     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.73/0.91  thf('10', plain,
% 0.73/0.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.73/0.91         ((k2_enumset1 @ X3 @ X4 @ X6 @ X5) = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 0.73/0.91      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.73/0.91  thf('11', plain,
% 0.73/0.91      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.73/0.91         ((k2_enumset1 @ X23 @ X23 @ X24 @ X25)
% 0.73/0.91           = (k1_enumset1 @ X23 @ X24 @ X25))),
% 0.73/0.91      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.73/0.91  thf('12', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.91         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.73/0.91      inference('sup+', [status(thm)], ['10', '11'])).
% 0.73/0.91  thf('13', plain,
% 0.73/0.91      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.73/0.91         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.73/0.91           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.73/0.91              (k1_tarski @ X11)))),
% 0.73/0.91      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.73/0.91  thf('14', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3)
% 0.73/0.91           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.73/0.91      inference('sup+', [status(thm)], ['12', '13'])).
% 0.73/0.91  thf('15', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.73/0.91           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.73/0.91      inference('sup+', [status(thm)], ['4', '5'])).
% 0.73/0.91  thf('16', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3)
% 0.73/0.91           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 0.73/0.91      inference('demod', [status(thm)], ['14', '15'])).
% 0.73/0.91  thf('17', plain,
% 0.73/0.91      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.73/0.91         ((k3_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29)
% 0.73/0.91           = (k2_enumset1 @ X26 @ X27 @ X28 @ X29))),
% 0.73/0.91      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.73/0.91  thf('18', plain,
% 0.73/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.73/0.91         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 0.73/0.91      inference('sup+', [status(thm)], ['16', '17'])).
% 0.73/0.91  thf('19', plain,
% 0.73/0.91      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.73/0.91         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.73/0.91      inference('demod', [status(thm)], ['0', '9', '18'])).
% 0.73/0.91  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.73/0.91  
% 0.73/0.91  % SZS output end Refutation
% 0.73/0.91  
% 0.73/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
