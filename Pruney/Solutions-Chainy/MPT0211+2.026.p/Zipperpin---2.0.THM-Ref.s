%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.93OCZiWBMt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:33 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 134 expanded)
%              Number of leaves         :   16 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  425 (1337 expanded)
%              Number of equality atoms :   40 ( 125 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X15 @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X24 @ X26 @ X25 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('3',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X39 @ X38 @ X37 @ X36 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k2_enumset1 @ X61 @ X61 @ X62 @ X63 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k1_enumset1 @ sk_A @ sk_C @ sk_B )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X31 @ X30 @ X29 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('9',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k2_enumset1 @ X61 @ X61 @ X62 @ X63 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(l129_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ A @ D ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X13 @ X12 @ X11 @ X14 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l129_enumset1])).

thf('12',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k2_enumset1 @ X61 @ X61 @ X62 @ X63 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('15',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X49 @ X50 @ X51 ) @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X49 @ X50 @ X51 ) @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('22',plain,(
    ( k1_enumset1 @ sk_C @ sk_A @ sk_B )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['7','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X31 @ X30 @ X29 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('30',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['22','27','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.93OCZiWBMt
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.75  % Solved by: fo/fo7.sh
% 0.56/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.75  % done 278 iterations in 0.305s
% 0.56/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.75  % SZS output start Refutation
% 0.56/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.56/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.56/0.75  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.56/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.75  thf(t137_enumset1, conjecture,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.56/0.75       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.56/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.75        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.56/0.75          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.56/0.75    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.56/0.75  thf('0', plain,
% 0.56/0.75      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.56/0.75         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(l53_enumset1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.56/0.75       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.56/0.75  thf('1', plain,
% 0.56/0.75      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X15 @ X16 @ X17 @ X18)
% 0.56/0.75           = (k2_xboole_0 @ (k2_tarski @ X15 @ X16) @ (k2_tarski @ X17 @ X18)))),
% 0.56/0.75      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.56/0.75  thf(t104_enumset1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.56/0.75  thf('2', plain,
% 0.56/0.75      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X24 @ X26 @ X25 @ X27)
% 0.56/0.75           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 0.56/0.75      inference('cnf', [status(esa)], [t104_enumset1])).
% 0.56/0.75  thf('3', plain,
% 0.56/0.75      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 0.56/0.75         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.56/0.75  thf(t125_enumset1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.56/0.75  thf('4', plain,
% 0.56/0.75      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X39 @ X38 @ X37 @ X36)
% 0.56/0.75           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 0.56/0.75      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.56/0.75  thf(t71_enumset1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.56/0.75  thf('5', plain,
% 0.56/0.75      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X61 @ X61 @ X62 @ X63)
% 0.56/0.75           = (k1_enumset1 @ X61 @ X62 @ X63))),
% 0.56/0.75      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.75  thf('6', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.75      inference('sup+', [status(thm)], ['4', '5'])).
% 0.56/0.75  thf('7', plain,
% 0.56/0.75      (((k1_enumset1 @ sk_A @ sk_C @ sk_B)
% 0.56/0.75         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['3', '6'])).
% 0.56/0.75  thf(t107_enumset1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.56/0.75  thf('8', plain,
% 0.56/0.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X28 @ X31 @ X30 @ X29)
% 0.56/0.75           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 0.56/0.75      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.56/0.75  thf('9', plain,
% 0.56/0.75      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X61 @ X61 @ X62 @ X63)
% 0.56/0.75           = (k1_enumset1 @ X61 @ X62 @ X63))),
% 0.56/0.75      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.75  thf('10', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.75      inference('sup+', [status(thm)], ['8', '9'])).
% 0.56/0.75  thf(l129_enumset1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ A @ D ) ))).
% 0.56/0.75  thf('11', plain,
% 0.56/0.75      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X13 @ X12 @ X11 @ X14)
% 0.56/0.75           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.56/0.75      inference('cnf', [status(esa)], [l129_enumset1])).
% 0.56/0.75  thf('12', plain,
% 0.56/0.75      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X61 @ X61 @ X62 @ X63)
% 0.56/0.75           = (k1_enumset1 @ X61 @ X62 @ X63))),
% 0.56/0.75      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.56/0.75  thf('13', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('14', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 0.56/0.75      inference('sup+', [status(thm)], ['10', '13'])).
% 0.56/0.75  thf(t46_enumset1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.56/0.75       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.56/0.75  thf('15', plain,
% 0.56/0.75      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X49 @ X50 @ X51 @ X52)
% 0.56/0.75           = (k2_xboole_0 @ (k1_enumset1 @ X49 @ X50 @ X51) @ (k1_tarski @ X52)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.56/0.75  thf('16', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2)
% 0.56/0.75           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 0.56/0.75      inference('sup+', [status(thm)], ['14', '15'])).
% 0.56/0.75  thf('17', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('18', plain,
% 0.56/0.75      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X49 @ X50 @ X51 @ X52)
% 0.56/0.75           = (k2_xboole_0 @ (k1_enumset1 @ X49 @ X50 @ X51) @ (k1_tarski @ X52)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.56/0.75  thf('19', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('20', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.75      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.56/0.75  thf('21', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.75      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.56/0.75  thf('22', plain,
% 0.56/0.75      (((k1_enumset1 @ sk_C @ sk_A @ sk_B)
% 0.56/0.75         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.56/0.75      inference('demod', [status(thm)], ['7', '20', '21'])).
% 0.56/0.75  thf('23', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('24', plain,
% 0.56/0.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X28 @ X31 @ X30 @ X29)
% 0.56/0.75           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 0.56/0.75      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.56/0.75  thf('25', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X1 @ X0 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.56/0.75      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.75  thf('26', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.75      inference('sup+', [status(thm)], ['4', '5'])).
% 0.56/0.75  thf('27', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.56/0.75      inference('sup+', [status(thm)], ['25', '26'])).
% 0.56/0.75  thf('28', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.56/0.75      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.56/0.75  thf('29', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.56/0.75      inference('sup+', [status(thm)], ['25', '26'])).
% 0.56/0.75  thf('30', plain,
% 0.56/0.75      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.56/0.75         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['22', '27', '28', '29'])).
% 0.56/0.75  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.56/0.75  
% 0.56/0.75  % SZS output end Refutation
% 0.56/0.75  
% 0.62/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
