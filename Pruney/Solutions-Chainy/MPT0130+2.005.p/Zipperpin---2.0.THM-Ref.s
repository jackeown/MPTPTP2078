%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NsMjmSUuZ6

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:57 EST 2020

% Result     : Theorem 8.05s
% Output     : Refutation 8.05s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  510 ( 734 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t46_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ X3 @ ( k1_tarski @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X3 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X3 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X3 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NsMjmSUuZ6
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.05/8.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.05/8.29  % Solved by: fo/fo7.sh
% 8.05/8.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.05/8.29  % done 6759 iterations in 7.833s
% 8.05/8.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.05/8.29  % SZS output start Refutation
% 8.05/8.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.05/8.29  thf(sk_B_type, type, sk_B: $i).
% 8.05/8.29  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.05/8.29  thf(sk_D_type, type, sk_D: $i).
% 8.05/8.29  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.05/8.29  thf(sk_A_type, type, sk_A: $i).
% 8.05/8.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.05/8.29  thf(sk_C_type, type, sk_C: $i).
% 8.05/8.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.05/8.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.05/8.29  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 8.05/8.29  thf(t46_enumset1, conjecture,
% 8.05/8.29    (![A:$i,B:$i,C:$i,D:$i]:
% 8.05/8.29     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 8.05/8.29       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 8.05/8.29  thf(zf_stmt_0, negated_conjecture,
% 8.05/8.29    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 8.05/8.29        ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 8.05/8.29          ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )),
% 8.05/8.29    inference('cnf.neg', [status(esa)], [t46_enumset1])).
% 8.05/8.29  thf('0', plain,
% 8.05/8.29      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.05/8.29         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 8.05/8.29             (k1_tarski @ sk_D)))),
% 8.05/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.05/8.29  thf(t42_enumset1, axiom,
% 8.05/8.29    (![A:$i,B:$i,C:$i]:
% 8.05/8.29     ( ( k1_enumset1 @ A @ B @ C ) =
% 8.05/8.29       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 8.05/8.29  thf('1', plain,
% 8.05/8.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.05/8.29         ((k1_enumset1 @ X25 @ X26 @ X27)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t42_enumset1])).
% 8.05/8.29  thf(t4_xboole_1, axiom,
% 8.05/8.29    (![A:$i,B:$i,C:$i]:
% 8.05/8.29     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 8.05/8.29       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.05/8.29  thf('2', plain,
% 8.05/8.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 8.05/8.29           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t4_xboole_1])).
% 8.05/8.29  thf(t40_xboole_1, axiom,
% 8.05/8.29    (![A:$i,B:$i]:
% 8.05/8.29     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 8.05/8.29  thf('3', plain,
% 8.05/8.29      (![X4 : $i, X5 : $i]:
% 8.05/8.29         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 8.05/8.29           = (k4_xboole_0 @ X4 @ X5))),
% 8.05/8.29      inference('cnf', [status(esa)], [t40_xboole_1])).
% 8.05/8.29  thf(t98_xboole_1, axiom,
% 8.05/8.29    (![A:$i,B:$i]:
% 8.05/8.29     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 8.05/8.29  thf('4', plain,
% 8.05/8.29      (![X21 : $i, X22 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ X21 @ X22)
% 8.05/8.29           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t98_xboole_1])).
% 8.05/8.29  thf('5', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 8.05/8.29           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['3', '4'])).
% 8.05/8.29  thf('6', plain,
% 8.05/8.29      (![X21 : $i, X22 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ X21 @ X22)
% 8.05/8.29           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t98_xboole_1])).
% 8.05/8.29  thf('7', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 8.05/8.29           = (k2_xboole_0 @ X0 @ X1))),
% 8.05/8.29      inference('demod', [status(thm)], ['5', '6'])).
% 8.05/8.29  thf('8', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 8.05/8.29           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['2', '7'])).
% 8.05/8.29  thf('9', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 8.05/8.29           (k2_xboole_0 @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0)))
% 8.05/8.29           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 8.05/8.29              (k2_xboole_0 @ X3 @ (k1_tarski @ X2))))),
% 8.05/8.29      inference('sup+', [status(thm)], ['1', '8'])).
% 8.05/8.29  thf(t41_enumset1, axiom,
% 8.05/8.29    (![A:$i,B:$i]:
% 8.05/8.29     ( ( k2_tarski @ A @ B ) =
% 8.05/8.29       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 8.05/8.29  thf('10', plain,
% 8.05/8.29      (![X23 : $i, X24 : $i]:
% 8.05/8.29         ((k2_tarski @ X23 @ X24)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t41_enumset1])).
% 8.05/8.29  thf('11', plain,
% 8.05/8.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 8.05/8.29           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t4_xboole_1])).
% 8.05/8.29  thf('12', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 8.05/8.29              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['10', '11'])).
% 8.05/8.29  thf('13', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 8.05/8.29              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['10', '11'])).
% 8.05/8.29  thf('14', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 8.05/8.29           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 8.05/8.29              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['12', '13'])).
% 8.05/8.29  thf('15', plain,
% 8.05/8.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.05/8.29         ((k1_enumset1 @ X25 @ X26 @ X27)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t42_enumset1])).
% 8.05/8.29  thf('16', plain,
% 8.05/8.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 8.05/8.29           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t4_xboole_1])).
% 8.05/8.29  thf('17', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 8.05/8.29              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['15', '16'])).
% 8.05/8.29  thf('18', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 8.05/8.29           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 8.05/8.29           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ X0))),
% 8.05/8.29      inference('demod', [status(thm)], ['14', '17'])).
% 8.05/8.29  thf('19', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 8.05/8.29           (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))
% 8.05/8.29           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X3) @ (k1_tarski @ X2)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['9', '18'])).
% 8.05/8.29  thf('20', plain,
% 8.05/8.29      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.05/8.29         ((k1_enumset1 @ X25 @ X26 @ X27)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t42_enumset1])).
% 8.05/8.29  thf('21', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 8.05/8.29              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['10', '11'])).
% 8.05/8.29  thf('22', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['20', '21'])).
% 8.05/8.29  thf(t45_enumset1, axiom,
% 8.05/8.29    (![A:$i,B:$i,C:$i,D:$i]:
% 8.05/8.29     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 8.05/8.29       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 8.05/8.29  thf('23', plain,
% 8.05/8.29      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 8.05/8.29         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 8.05/8.29           = (k2_xboole_0 @ (k2_tarski @ X28 @ X29) @ (k2_tarski @ X30 @ X31)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t45_enumset1])).
% 8.05/8.29  thf('24', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 8.05/8.29           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 8.05/8.29      inference('demod', [status(thm)], ['22', '23'])).
% 8.05/8.29  thf('25', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 8.05/8.29           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 8.05/8.29           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X3) @ (k1_tarski @ X2)))),
% 8.05/8.29      inference('demod', [status(thm)], ['19', '24'])).
% 8.05/8.29  thf('26', plain,
% 8.05/8.29      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 8.05/8.29         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 8.05/8.29           = (k2_xboole_0 @ (k2_tarski @ X28 @ X29) @ (k2_tarski @ X30 @ X31)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t45_enumset1])).
% 8.05/8.29  thf('27', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 8.05/8.29           = (k2_xboole_0 @ X0 @ X1))),
% 8.05/8.29      inference('demod', [status(thm)], ['5', '6'])).
% 8.05/8.29  thf('28', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 8.05/8.29           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 8.05/8.29           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 8.05/8.29      inference('sup+', [status(thm)], ['26', '27'])).
% 8.05/8.29  thf('29', plain,
% 8.05/8.29      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 8.05/8.29         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 8.05/8.29           = (k2_xboole_0 @ (k2_tarski @ X28 @ X29) @ (k2_tarski @ X30 @ X31)))),
% 8.05/8.29      inference('cnf', [status(esa)], [t45_enumset1])).
% 8.05/8.29  thf('30', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 8.05/8.29           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 8.05/8.29           = (k2_enumset1 @ X1 @ X0 @ X3 @ X2))),
% 8.05/8.29      inference('demod', [status(thm)], ['28', '29'])).
% 8.05/8.29  thf('31', plain,
% 8.05/8.29      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.05/8.29         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 8.05/8.29           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X3) @ (k1_tarski @ X2)))),
% 8.05/8.29      inference('demod', [status(thm)], ['25', '30'])).
% 8.05/8.29  thf('32', plain,
% 8.05/8.29      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.05/8.29         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 8.05/8.29      inference('demod', [status(thm)], ['0', '31'])).
% 8.05/8.29  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 8.05/8.29  
% 8.05/8.29  % SZS output end Refutation
% 8.05/8.29  
% 8.05/8.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
