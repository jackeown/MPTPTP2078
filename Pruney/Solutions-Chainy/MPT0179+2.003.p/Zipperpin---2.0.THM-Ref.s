%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YpaSltjixd

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  59 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  408 ( 737 expanded)
%              Number of equality atoms :   29 (  49 expanded)
%              Maximal formula depth    :   18 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t95_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t95_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf('2',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t89_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X30 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t89_enumset1])).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','7'])).

thf(t83_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t49_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t49_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X30 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(demod,[status(thm)],['9','18'])).

thf('20',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YpaSltjixd
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.43  % Solved by: fo/fo7.sh
% 0.19/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.43  % done 14 iterations in 0.016s
% 0.19/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.43  % SZS output start Refutation
% 0.19/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.43  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.43  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.19/0.43                                           $i > $i).
% 0.19/0.43  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.43  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.43  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.43  thf(t95_enumset1, conjecture,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.43    (~( ![A:$i,B:$i]:
% 0.19/0.43        ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B ) =
% 0.19/0.43          ( k2_tarski @ A @ B ) ) )),
% 0.19/0.43    inference('cnf.neg', [status(esa)], [t95_enumset1])).
% 0.19/0.43  thf('0', plain,
% 0.19/0.43      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.19/0.43         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(t81_enumset1, axiom,
% 0.19/0.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.43     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.19/0.43       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.19/0.43  thf('1', plain,
% 0.19/0.43      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.43         ((k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.19/0.43           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.19/0.43      inference('cnf', [status(esa)], [t81_enumset1])).
% 0.19/0.43  thf('2', plain,
% 0.19/0.43      (((k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.19/0.43         != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.43  thf(t89_enumset1, axiom,
% 0.19/0.43    (![A:$i,B:$i,C:$i]:
% 0.19/0.43     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C ) =
% 0.19/0.43       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.43  thf('3', plain,
% 0.19/0.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.43         ((k5_enumset1 @ X30 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32)
% 0.19/0.43           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.19/0.43      inference('cnf', [status(esa)], [t89_enumset1])).
% 0.19/0.43  thf('4', plain,
% 0.19/0.43      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.43         ((k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.19/0.43           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.19/0.43      inference('cnf', [status(esa)], [t81_enumset1])).
% 0.19/0.43  thf(t75_enumset1, axiom,
% 0.19/0.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.43     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.19/0.43       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.19/0.43  thf('5', plain,
% 0.19/0.43      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.43         ((k6_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.19/0.43           = (k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.19/0.43      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.19/0.43  thf('6', plain,
% 0.19/0.43      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.43         ((k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.19/0.43           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.19/0.43      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.43  thf('7', plain,
% 0.19/0.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.43         ((k4_enumset1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32)
% 0.19/0.43           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.19/0.43      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.43  thf('8', plain,
% 0.19/0.43      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('demod', [status(thm)], ['2', '7'])).
% 0.19/0.43  thf(t83_enumset1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( k3_enumset1 @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.43  thf('9', plain,
% 0.19/0.43      (![X28 : $i, X29 : $i]:
% 0.19/0.43         ((k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.19/0.43      inference('cnf', [status(esa)], [t83_enumset1])).
% 0.19/0.43  thf('10', plain,
% 0.19/0.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.43         ((k4_enumset1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32)
% 0.19/0.43           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.19/0.43      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.43  thf('11', plain,
% 0.19/0.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.43         ((k4_enumset1 @ X30 @ X30 @ X30 @ X30 @ X31 @ X32)
% 0.19/0.43           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.19/0.43      inference('demod', [status(thm)], ['3', '6'])).
% 0.19/0.43  thf(t67_enumset1, axiom,
% 0.19/0.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.19/0.43     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.19/0.43       ( k2_xboole_0 @
% 0.19/0.43         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.19/0.43  thf('12', plain,
% 0.19/0.43      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.19/0.43         X14 : $i]:
% 0.19/0.43         ((k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.19/0.43           = (k2_xboole_0 @ (k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 0.19/0.43              (k2_tarski @ X13 @ X14)))),
% 0.19/0.43      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.19/0.43  thf('13', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.43         ((k6_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 0.19/0.43           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.19/0.43              (k2_tarski @ X4 @ X3)))),
% 0.19/0.43      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.43  thf('14', plain,
% 0.19/0.43      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.43         ((k6_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.19/0.43           = (k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.19/0.43      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.19/0.43  thf('15', plain,
% 0.19/0.43      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.43         ((k5_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.19/0.43           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.19/0.43      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.43  thf(t49_enumset1, axiom,
% 0.19/0.43    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.43     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.19/0.43       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.19/0.43  thf('16', plain,
% 0.19/0.43      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.43         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.19/0.43           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.19/0.43              (k2_tarski @ X5 @ X6)))),
% 0.19/0.43      inference('cnf', [status(esa)], [t49_enumset1])).
% 0.19/0.43  thf('17', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.43         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 0.19/0.43           = (k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 0.19/0.43      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.19/0.43  thf('18', plain,
% 0.19/0.43      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.43         ((k3_enumset1 @ X30 @ X30 @ X30 @ X31 @ X32)
% 0.19/0.43           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.19/0.43      inference('demod', [status(thm)], ['10', '17'])).
% 0.19/0.43  thf('19', plain,
% 0.19/0.43      (![X28 : $i, X29 : $i]:
% 0.19/0.43         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.19/0.43      inference('demod', [status(thm)], ['9', '18'])).
% 0.19/0.43  thf('20', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.43      inference('demod', [status(thm)], ['8', '19'])).
% 0.19/0.43  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.19/0.43  
% 0.19/0.43  % SZS output end Refutation
% 0.19/0.43  
% 0.19/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
