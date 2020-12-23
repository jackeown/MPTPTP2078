%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vsqCNff93D

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:58 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   40 (  51 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :  273 ( 359 expanded)
%              Number of equality atoms :   31 (  42 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X18 @ X17 @ X16 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X18 @ X17 @ X16 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('21',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','9','18','19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vsqCNff93D
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 346 iterations in 0.171s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(t32_zfmisc_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.41/0.62       ( k2_tarski @ A @ B ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.41/0.62          ( k2_tarski @ A @ B ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.41/0.62         != (k2_tarski @ sk_A @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(l51_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X47 : $i, X48 : $i]:
% 0.41/0.62         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.41/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.41/0.62         != (k2_tarski @ sk_A @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.62  thf(t69_enumset1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.62  thf('3', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf('4', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf(l53_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.41/0.62       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf(t71_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.62         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.41/0.62           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.41/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['3', '8'])).
% 0.41/0.62  thf(t70_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.62  thf(commutativity_k2_tarski, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.62  thf(t102_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X18 @ X17 @ X16) = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X18 @ X17 @ X16) = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.41/0.62      inference('sup+', [status(thm)], ['15', '16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['14', '17'])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.62  thf('21', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['2', '9', '18', '19', '20'])).
% 0.41/0.62  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
