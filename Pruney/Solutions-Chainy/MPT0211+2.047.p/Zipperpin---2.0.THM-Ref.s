%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTUySvcOYz

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:36 EST 2020

% Result     : Theorem 6.25s
% Output     : Refutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 133 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  477 (1325 expanded)
%              Number of equality atoms :   44 ( 123 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t117_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ D @ A ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X25 @ X24 @ X26 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

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
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X19 @ X18 @ X17 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('5',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('8',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X27 @ X25 @ X24 @ X26 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf('16',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X23 @ X20 @ X22 @ X21 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('19',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('25',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['14','23','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X11 @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('30',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 )
      = ( k2_enumset1 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('33',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','28','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pTUySvcOYz
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.25/6.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.25/6.46  % Solved by: fo/fo7.sh
% 6.25/6.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.25/6.46  % done 3488 iterations in 6.011s
% 6.25/6.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.25/6.46  % SZS output start Refutation
% 6.25/6.46  thf(sk_B_type, type, sk_B: $i).
% 6.25/6.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.25/6.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.25/6.46  thf(sk_A_type, type, sk_A: $i).
% 6.25/6.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.25/6.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.25/6.46  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.25/6.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.25/6.46  thf(sk_C_type, type, sk_C: $i).
% 6.25/6.46  thf(t137_enumset1, conjecture,
% 6.25/6.46    (![A:$i,B:$i,C:$i]:
% 6.25/6.46     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.25/6.46       ( k1_enumset1 @ A @ B @ C ) ))).
% 6.25/6.46  thf(zf_stmt_0, negated_conjecture,
% 6.25/6.46    (~( ![A:$i,B:$i,C:$i]:
% 6.25/6.46        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 6.25/6.46          ( k1_enumset1 @ A @ B @ C ) ) )),
% 6.25/6.46    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 6.25/6.46  thf('0', plain,
% 6.25/6.46      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 6.25/6.46         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 6.25/6.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.25/6.46  thf(t117_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i,C:$i,D:$i]:
% 6.25/6.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ))).
% 6.25/6.46  thf('1', plain,
% 6.25/6.46      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X27 @ X25 @ X24 @ X26)
% 6.25/6.46           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.25/6.46      inference('cnf', [status(esa)], [t117_enumset1])).
% 6.25/6.46  thf(t71_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i,C:$i]:
% 6.25/6.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 6.25/6.46  thf('2', plain,
% 6.25/6.46      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.25/6.46           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.25/6.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.25/6.46  thf('3', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.25/6.46      inference('sup+', [status(thm)], ['1', '2'])).
% 6.25/6.46  thf(t107_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i,C:$i,D:$i]:
% 6.25/6.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 6.25/6.46  thf('4', plain,
% 6.25/6.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X16 @ X19 @ X18 @ X17)
% 6.25/6.46           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 6.25/6.46      inference('cnf', [status(esa)], [t107_enumset1])).
% 6.25/6.46  thf('5', plain,
% 6.25/6.46      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.25/6.46           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.25/6.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.25/6.46  thf('6', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.25/6.46      inference('sup+', [status(thm)], ['4', '5'])).
% 6.25/6.46  thf('7', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 6.25/6.46      inference('sup+', [status(thm)], ['3', '6'])).
% 6.25/6.46  thf(t46_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i,C:$i,D:$i]:
% 6.25/6.46     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 6.25/6.46       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 6.25/6.46  thf('8', plain,
% 6.25/6.46      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 6.25/6.46           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 6.25/6.46      inference('cnf', [status(esa)], [t46_enumset1])).
% 6.25/6.46  thf('9', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2)
% 6.25/6.46           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 6.25/6.46      inference('sup+', [status(thm)], ['7', '8'])).
% 6.25/6.46  thf('10', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.25/6.46      inference('sup+', [status(thm)], ['1', '2'])).
% 6.25/6.46  thf('11', plain,
% 6.25/6.46      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 6.25/6.46           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 6.25/6.46      inference('cnf', [status(esa)], [t46_enumset1])).
% 6.25/6.46  thf('12', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 6.25/6.46      inference('sup+', [status(thm)], ['1', '2'])).
% 6.25/6.46  thf('13', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 6.25/6.46      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 6.25/6.46  thf('14', plain,
% 6.25/6.46      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 6.25/6.46         != (k1_enumset1 @ sk_C @ sk_B @ sk_A))),
% 6.25/6.46      inference('demod', [status(thm)], ['0', '13'])).
% 6.25/6.46  thf('15', plain,
% 6.25/6.46      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X27 @ X25 @ X24 @ X26)
% 6.25/6.46           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.25/6.46      inference('cnf', [status(esa)], [t117_enumset1])).
% 6.25/6.46  thf('16', plain,
% 6.25/6.46      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.25/6.46           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.25/6.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.25/6.46  thf('17', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 6.25/6.46      inference('sup+', [status(thm)], ['15', '16'])).
% 6.25/6.46  thf(t113_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i,C:$i,D:$i]:
% 6.25/6.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 6.25/6.46  thf('18', plain,
% 6.25/6.46      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X23 @ X20 @ X22 @ X21)
% 6.25/6.46           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 6.25/6.46      inference('cnf', [status(esa)], [t113_enumset1])).
% 6.25/6.46  thf('19', plain,
% 6.25/6.46      (![X48 : $i, X49 : $i, X50 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 6.25/6.46           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 6.25/6.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.25/6.46  thf('20', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.25/6.46      inference('sup+', [status(thm)], ['18', '19'])).
% 6.25/6.46  thf('21', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 6.25/6.46      inference('sup+', [status(thm)], ['17', '20'])).
% 6.25/6.46  thf('22', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 6.25/6.46      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 6.25/6.46  thf('23', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.25/6.46      inference('sup+', [status(thm)], ['21', '22'])).
% 6.25/6.46  thf('24', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 6.25/6.46      inference('sup+', [status(thm)], ['17', '20'])).
% 6.25/6.46  thf('25', plain,
% 6.25/6.46      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 6.25/6.46         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 6.25/6.46      inference('demod', [status(thm)], ['14', '23', '24'])).
% 6.25/6.46  thf(t70_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.25/6.46  thf('26', plain,
% 6.25/6.46      (![X46 : $i, X47 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 6.25/6.46      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.25/6.46  thf(l57_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.25/6.46     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 6.25/6.46       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 6.25/6.46  thf('27', plain,
% 6.25/6.46      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 6.25/6.46         ((k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15)
% 6.25/6.46           = (k2_xboole_0 @ (k1_enumset1 @ X11 @ X12 @ X13) @ 
% 6.25/6.46              (k2_tarski @ X14 @ X15)))),
% 6.25/6.46      inference('cnf', [status(esa)], [l57_enumset1])).
% 6.25/6.46  thf('28', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.25/6.46         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 6.25/6.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 6.25/6.46      inference('sup+', [status(thm)], ['26', '27'])).
% 6.25/6.46  thf('29', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 6.25/6.46      inference('sup+', [status(thm)], ['18', '19'])).
% 6.25/6.46  thf(t72_enumset1, axiom,
% 6.25/6.46    (![A:$i,B:$i,C:$i,D:$i]:
% 6.25/6.46     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.25/6.46  thf('30', plain,
% 6.25/6.46      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 6.25/6.46         ((k3_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54)
% 6.25/6.46           = (k2_enumset1 @ X51 @ X52 @ X53 @ X54))),
% 6.25/6.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.25/6.46  thf('31', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.25/6.46      inference('sup+', [status(thm)], ['29', '30'])).
% 6.25/6.46  thf('32', plain,
% 6.25/6.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.25/6.46         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 6.25/6.46      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 6.25/6.46  thf('33', plain,
% 6.25/6.46      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 6.25/6.46         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 6.25/6.46      inference('demod', [status(thm)], ['25', '28', '31', '32'])).
% 6.25/6.46  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 6.25/6.46  
% 6.25/6.46  % SZS output end Refutation
% 6.25/6.46  
% 6.25/6.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
