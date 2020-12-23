%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zMukzfLmIp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:07 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   48 (  79 expanded)
%              Number of leaves         :   18 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  417 ( 776 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X39 @ X39 @ X40 @ X41 )
      = ( k1_enumset1 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_enumset1 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X5 @ X4 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('10',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X39 @ X39 @ X40 @ X41 )
      = ( k1_enumset1 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_enumset1 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X5 @ X4 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','23','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zMukzfLmIp
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:39:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1581 iterations in 0.810s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.06/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.25  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.06/1.25  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.25  thf(sk_D_type, type, sk_D: $i).
% 1.06/1.25  thf(t108_enumset1, conjecture,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 1.06/1.25  thf('0', plain,
% 1.06/1.25      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.06/1.25         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(commutativity_k2_tarski, axiom,
% 1.06/1.25    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.06/1.25  thf('1', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.06/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.25  thf(t70_enumset1, axiom,
% 1.06/1.25    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.06/1.25  thf('2', plain,
% 1.06/1.25      (![X37 : $i, X38 : $i]:
% 1.06/1.25         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 1.06/1.25      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.06/1.25  thf(t71_enumset1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.06/1.25  thf('3', plain,
% 1.06/1.25      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X39 @ X39 @ X40 @ X41)
% 1.06/1.25           = (k1_enumset1 @ X39 @ X40 @ X41))),
% 1.06/1.25      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.06/1.25  thf(t50_enumset1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.06/1.25     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 1.06/1.25       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 1.06/1.25  thf('4', plain,
% 1.06/1.25      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.25         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 1.06/1.25           = (k2_xboole_0 @ (k2_enumset1 @ X15 @ X16 @ X17 @ X18) @ 
% 1.06/1.25              (k1_tarski @ X19)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t50_enumset1])).
% 1.06/1.25  thf('5', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 1.06/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['3', '4'])).
% 1.06/1.25  thf(t72_enumset1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.06/1.25  thf('6', plain,
% 1.06/1.25      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.06/1.25         ((k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45)
% 1.06/1.25           = (k2_enumset1 @ X42 @ X43 @ X44 @ X45))),
% 1.06/1.25      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.06/1.25  thf('7', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 1.06/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.06/1.25      inference('demod', [status(thm)], ['5', '6'])).
% 1.06/1.25  thf('8', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.06/1.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['2', '7'])).
% 1.06/1.25  thf(t103_enumset1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X2 @ X3 @ X5 @ X4) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 1.06/1.25      inference('cnf', [status(esa)], [t103_enumset1])).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X39 @ X39 @ X40 @ X41)
% 1.06/1.25           = (k1_enumset1 @ X39 @ X40 @ X41))),
% 1.06/1.25      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.06/1.25  thf('11', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 1.06/1.25      inference('sup+', [status(thm)], ['9', '10'])).
% 1.06/1.25  thf('12', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k1_enumset1 @ X1 @ X2 @ X0)
% 1.06/1.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.06/1.25      inference('demod', [status(thm)], ['8', '11'])).
% 1.06/1.25  thf('13', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k1_enumset1 @ X0 @ X2 @ X1)
% 1.06/1.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['1', '12'])).
% 1.06/1.25  thf('14', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k1_enumset1 @ X1 @ X2 @ X0)
% 1.06/1.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.06/1.25      inference('demod', [status(thm)], ['8', '11'])).
% 1.06/1.25  thf('15', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['13', '14'])).
% 1.06/1.25  thf('16', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 1.06/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.06/1.25      inference('demod', [status(thm)], ['5', '6'])).
% 1.06/1.25  thf('17', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 1.06/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['15', '16'])).
% 1.06/1.25  thf('18', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 1.06/1.25      inference('sup+', [status(thm)], ['9', '10'])).
% 1.06/1.25  thf('19', plain,
% 1.06/1.25      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.25         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 1.06/1.25           = (k2_xboole_0 @ (k2_enumset1 @ X15 @ X16 @ X17 @ X18) @ 
% 1.06/1.25              (k1_tarski @ X19)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t50_enumset1])).
% 1.06/1.25  thf('20', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k3_enumset1 @ X2 @ X2 @ X0 @ X1 @ X3)
% 1.06/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['18', '19'])).
% 1.06/1.25  thf('21', plain,
% 1.06/1.25      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.06/1.25         ((k3_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45)
% 1.06/1.25           = (k2_enumset1 @ X42 @ X43 @ X44 @ X45))),
% 1.06/1.25      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.06/1.25  thf('22', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X2 @ X0 @ X1 @ X3)
% 1.06/1.25           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.06/1.25      inference('demod', [status(thm)], ['20', '21'])).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['17', '22'])).
% 1.06/1.25  thf(t105_enumset1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 1.06/1.25  thf('24', plain,
% 1.06/1.25      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 1.06/1.25      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.06/1.25  thf('25', plain,
% 1.06/1.25      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X2 @ X3 @ X5 @ X4) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 1.06/1.25      inference('cnf', [status(esa)], [t103_enumset1])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['24', '25'])).
% 1.06/1.25  thf('27', plain,
% 1.06/1.25      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 1.06/1.25         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 1.06/1.25      inference('demod', [status(thm)], ['0', '23', '26'])).
% 1.06/1.25  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 1.06/1.25  
% 1.06/1.25  % SZS output end Refutation
% 1.06/1.25  
% 1.06/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
