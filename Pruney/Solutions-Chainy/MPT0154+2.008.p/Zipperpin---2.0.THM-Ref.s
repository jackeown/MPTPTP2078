%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YlsnolTGnX

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  331 ( 448 expanded)
%              Number of equality atoms :   41 (  58 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YlsnolTGnX
% 0.15/0.37  % Computer   : n008.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:24:30 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 327 iterations in 0.171s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(t70_enumset1, conjecture,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(t41_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k2_tarski @ A @ B ) =
% 0.44/0.66       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X15 : $i, X16 : $i]:
% 0.44/0.66         ((k2_tarski @ X15 @ X16)
% 0.44/0.66           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.44/0.66  thf(t46_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      (![X6 : $i, X7 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.44/0.66           = (k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.44/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.66  thf(t100_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X4 : $i, X5 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X4 @ X5)
% 0.44/0.66           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.66  thf(t92_xboole_1, axiom,
% 0.44/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.44/0.66  thf('7', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.44/0.66  thf(t91_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.66       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.66         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.44/0.66           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.44/0.66           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['7', '8'])).
% 0.44/0.66  thf(commutativity_k5_xboole_0, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.44/0.66  thf(t5_boole, axiom,
% 0.44/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.66  thf('11', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.44/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.44/0.66  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['9', '12'])).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k3_xboole_0 @ X0 @ X1)
% 0.44/0.66           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['6', '13'])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.44/0.66           = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['3', '14'])).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.44/0.66  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['10', '11'])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.44/0.66           = (k1_tarski @ X1))),
% 0.44/0.66      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (![X4 : $i, X5 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X4 @ X5)
% 0.44/0.66           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.44/0.66      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['9', '12'])).
% 0.44/0.66  thf('22', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.44/0.66  thf('23', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((X1)
% 0.44/0.66           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['19', '22'])).
% 0.44/0.66  thf('24', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k2_tarski @ X0 @ X1)
% 0.44/0.66           = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.44/0.66              (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))))),
% 0.44/0.66      inference('sup+', [status(thm)], ['18', '23'])).
% 0.44/0.66  thf(t98_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.66  thf('25', plain,
% 0.44/0.66      (![X13 : $i, X14 : $i]:
% 0.44/0.66         ((k2_xboole_0 @ X13 @ X14)
% 0.44/0.66           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.66  thf(t42_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.44/0.66       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.44/0.66  thf('26', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.66         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.44/0.66           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k2_tarski @ X18 @ X19)))),
% 0.44/0.66      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.44/0.66  thf('27', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.44/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.66  thf('28', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.44/0.66      inference('demod', [status(thm)], ['0', '27'])).
% 0.44/0.66  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.49/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
