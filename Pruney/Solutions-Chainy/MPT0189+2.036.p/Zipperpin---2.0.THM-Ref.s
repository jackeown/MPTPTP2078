%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qLjQLvyqC4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:11 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  201 ( 289 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t99_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X41 @ X43 )
      = ( k1_enumset1 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X16 @ X16 @ X17 @ X18 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qLjQLvyqC4
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:58:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 126 iterations in 0.099s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.56  thf(t108_enumset1, conjecture,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.36/0.56         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t99_enumset1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.56         ((k1_enumset1 @ X42 @ X41 @ X43) = (k1_enumset1 @ X41 @ X42 @ X43))),
% 0.36/0.56      inference('cnf', [status(esa)], [t99_enumset1])).
% 0.36/0.56  thf(t71_enumset1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.56         ((k2_enumset1 @ X16 @ X16 @ X17 @ X18)
% 0.36/0.56           = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.56  thf(t50_enumset1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.56     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.36/0.56       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.56         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.36/0.56           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.36/0.56              (k1_tarski @ X4)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.36/0.56           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.56  thf(t72_enumset1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.56         ((k3_enumset1 @ X19 @ X19 @ X20 @ X21 @ X22)
% 0.36/0.56           = (k2_enumset1 @ X19 @ X20 @ X21 @ X22))),
% 0.36/0.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.56           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.36/0.56           = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 0.36/0.56      inference('sup+', [status(thm)], ['1', '6'])).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.56           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.36/0.56         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.36/0.56      inference('demod', [status(thm)], ['0', '9'])).
% 0.36/0.56  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
