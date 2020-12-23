%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AI58z7LMbD

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:56 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 115 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :  495 (1126 expanded)
%              Number of equality atoms :   44 ( 105 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('4',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['4','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X0 @ X2 ) @ ( k1_tarski @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X0 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['23','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AI58z7LMbD
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.05/2.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.05/2.30  % Solved by: fo/fo7.sh
% 2.05/2.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.30  % done 547 iterations in 1.845s
% 2.05/2.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.05/2.30  % SZS output start Refutation
% 2.05/2.30  thf(sk_C_type, type, sk_C: $i).
% 2.05/2.30  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.30  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.05/2.30  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.05/2.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.05/2.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.05/2.30  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.05/2.30  thf(sk_D_type, type, sk_D: $i).
% 2.05/2.30  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.30  thf(t46_enumset1, conjecture,
% 2.05/2.30    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.30     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.05/2.30       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 2.05/2.30  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.30    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.30        ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.05/2.30          ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )),
% 2.05/2.30    inference('cnf.neg', [status(esa)], [t46_enumset1])).
% 2.05/2.30  thf('0', plain,
% 2.05/2.30      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.05/2.30         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 2.05/2.30             (k1_tarski @ sk_D)))),
% 2.05/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.30  thf(commutativity_k2_xboole_0, axiom,
% 2.05/2.30    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.05/2.30  thf('1', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.30      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.05/2.30  thf('2', plain,
% 2.05/2.30      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.05/2.30         != (k2_xboole_0 @ (k1_tarski @ sk_D) @ 
% 2.05/2.30             (k1_enumset1 @ sk_A @ sk_B @ sk_C)))),
% 2.05/2.30      inference('demod', [status(thm)], ['0', '1'])).
% 2.05/2.30  thf(t44_enumset1, axiom,
% 2.05/2.30    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.30     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.05/2.30       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 2.05/2.30  thf('3', plain,
% 2.05/2.30      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t44_enumset1])).
% 2.05/2.30  thf('4', plain,
% 2.05/2.30      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.05/2.30         != (k2_enumset1 @ sk_D @ sk_A @ sk_B @ sk_C))),
% 2.05/2.30      inference('demod', [status(thm)], ['2', '3'])).
% 2.05/2.30  thf(t41_enumset1, axiom,
% 2.05/2.30    (![A:$i,B:$i]:
% 2.05/2.30     ( ( k2_tarski @ A @ B ) =
% 2.05/2.30       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 2.05/2.30  thf('5', plain,
% 2.05/2.30      (![X5 : $i, X6 : $i]:
% 2.05/2.30         ((k2_tarski @ X5 @ X6)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t41_enumset1])).
% 2.05/2.30  thf('6', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.30      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.05/2.30  thf('7', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 2.05/2.30           = (k2_tarski @ X1 @ X0))),
% 2.05/2.30      inference('sup+', [status(thm)], ['5', '6'])).
% 2.05/2.30  thf('8', plain,
% 2.05/2.30      (![X5 : $i, X6 : $i]:
% 2.05/2.30         ((k2_tarski @ X5 @ X6)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t41_enumset1])).
% 2.05/2.30  thf(t4_xboole_1, axiom,
% 2.05/2.30    (![A:$i,B:$i,C:$i]:
% 2.05/2.30     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.05/2.30       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.05/2.30  thf('9', plain,
% 2.05/2.30      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 2.05/2.30           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.05/2.30  thf('10', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 2.05/2.30              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 2.05/2.30      inference('sup+', [status(thm)], ['8', '9'])).
% 2.05/2.30  thf('11', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1))
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 2.05/2.30      inference('sup+', [status(thm)], ['7', '10'])).
% 2.05/2.30  thf(t42_enumset1, axiom,
% 2.05/2.30    (![A:$i,B:$i,C:$i]:
% 2.05/2.30     ( ( k1_enumset1 @ A @ B @ C ) =
% 2.05/2.30       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 2.05/2.30  thf('12', plain,
% 2.05/2.30      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.05/2.30         ((k1_enumset1 @ X7 @ X8 @ X9)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t42_enumset1])).
% 2.05/2.30  thf('13', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1))
% 2.05/2.30           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('demod', [status(thm)], ['11', '12'])).
% 2.05/2.30  thf('14', plain,
% 2.05/2.30      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.05/2.30         ((k1_enumset1 @ X7 @ X8 @ X9)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t42_enumset1])).
% 2.05/2.30  thf('15', plain,
% 2.05/2.30      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 2.05/2.30           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.05/2.30  thf('16', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 2.05/2.30              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 2.05/2.30      inference('sup+', [status(thm)], ['14', '15'])).
% 2.05/2.30  thf('17', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X0) @ (k1_tarski @ X1))
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 2.05/2.30      inference('sup+', [status(thm)], ['13', '16'])).
% 2.05/2.30  thf('18', plain,
% 2.05/2.30      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t44_enumset1])).
% 2.05/2.30  thf('19', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.30      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.05/2.30  thf('20', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 2.05/2.30           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('sup+', [status(thm)], ['18', '19'])).
% 2.05/2.30  thf('21', plain,
% 2.05/2.30      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t44_enumset1])).
% 2.05/2.30  thf('22', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('demod', [status(thm)], ['17', '20', '21'])).
% 2.05/2.30  thf('23', plain,
% 2.05/2.30      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.05/2.30         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 2.05/2.30      inference('demod', [status(thm)], ['4', '22'])).
% 2.05/2.30  thf('24', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 2.05/2.30           = (k2_tarski @ X1 @ X0))),
% 2.05/2.30      inference('sup+', [status(thm)], ['5', '6'])).
% 2.05/2.30  thf('25', plain,
% 2.05/2.30      (![X5 : $i, X6 : $i]:
% 2.05/2.30         ((k2_tarski @ X5 @ X6)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t41_enumset1])).
% 2.05/2.30  thf('26', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 2.05/2.30      inference('sup+', [status(thm)], ['24', '25'])).
% 2.05/2.30  thf('27', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1))
% 2.05/2.30           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('demod', [status(thm)], ['11', '12'])).
% 2.05/2.30  thf('28', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 2.05/2.30           = (k1_enumset1 @ X0 @ X2 @ X1))),
% 2.05/2.30      inference('sup+', [status(thm)], ['26', '27'])).
% 2.05/2.30  thf('29', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 2.05/2.30              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 2.05/2.30      inference('sup+', [status(thm)], ['14', '15'])).
% 2.05/2.30  thf('30', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X0 @ X2) @ (k1_tarski @ X1))
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 2.05/2.30      inference('sup+', [status(thm)], ['28', '29'])).
% 2.05/2.30  thf('31', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 2.05/2.30           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('sup+', [status(thm)], ['18', '19'])).
% 2.05/2.30  thf('32', plain,
% 2.05/2.30      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 2.05/2.30           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 2.05/2.30      inference('cnf', [status(esa)], [t44_enumset1])).
% 2.05/2.30  thf('33', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X1 @ X3 @ X0 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.05/2.30  thf('34', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('demod', [status(thm)], ['17', '20', '21'])).
% 2.05/2.30  thf('35', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.05/2.30         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.05/2.30      inference('sup+', [status(thm)], ['33', '34'])).
% 2.05/2.30  thf('36', plain,
% 2.05/2.30      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.05/2.30         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 2.05/2.30      inference('demod', [status(thm)], ['23', '35'])).
% 2.05/2.30  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 2.05/2.30  
% 2.05/2.30  % SZS output end Refutation
% 2.05/2.30  
% 2.14/2.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
