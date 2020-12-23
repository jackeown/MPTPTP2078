%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.neb9M9noBi

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:26 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  195 ( 203 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_enumset1 @ X10 @ X10 @ X11 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.neb9M9noBi
% 0.10/0.30  % Computer   : n011.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 12:49:27 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running portfolio for 600 s
% 0.10/0.30  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.10/0.30  % Number of cores: 8
% 0.10/0.31  % Python version: Python 3.6.8
% 0.10/0.31  % Running in FO mode
% 0.16/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.43  % Solved by: fo/fo7.sh
% 0.16/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.43  % done 47 iterations in 0.020s
% 0.16/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.43  % SZS output start Refutation
% 0.16/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.43  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.16/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.16/0.43  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.16/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.16/0.43  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.16/0.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.16/0.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.16/0.43  thf(t14_zfmisc_1, conjecture,
% 0.16/0.43    (![A:$i,B:$i]:
% 0.16/0.43     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.16/0.43       ( k2_tarski @ A @ B ) ))).
% 0.16/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.43    (~( ![A:$i,B:$i]:
% 0.16/0.43        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.16/0.43          ( k2_tarski @ A @ B ) ) )),
% 0.16/0.43    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.16/0.43  thf('0', plain,
% 0.16/0.43      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.16/0.43         != (k2_tarski @ sk_A @ sk_B))),
% 0.16/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.43  thf(t72_enumset1, axiom,
% 0.16/0.43    (![A:$i,B:$i,C:$i,D:$i]:
% 0.16/0.43     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.16/0.43  thf('1', plain,
% 0.16/0.43      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.16/0.43         ((k3_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18)
% 0.16/0.43           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.16/0.43      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.16/0.43  thf(t71_enumset1, axiom,
% 0.16/0.43    (![A:$i,B:$i,C:$i]:
% 0.16/0.43     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.16/0.43  thf('2', plain,
% 0.16/0.43      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.16/0.43         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.16/0.43           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.16/0.43      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.16/0.43  thf('3', plain,
% 0.16/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.16/0.43         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.16/0.43      inference('sup+', [status(thm)], ['1', '2'])).
% 0.16/0.43  thf(t70_enumset1, axiom,
% 0.16/0.43    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.16/0.43  thf('4', plain,
% 0.16/0.43      (![X10 : $i, X11 : $i]:
% 0.16/0.43         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 0.16/0.43      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.16/0.43  thf(t48_enumset1, axiom,
% 0.16/0.43    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.16/0.43     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.16/0.43       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.16/0.43  thf('5', plain,
% 0.16/0.43      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.16/0.43         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 0.16/0.43           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ 
% 0.16/0.43              (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.16/0.43      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.16/0.43  thf('6', plain,
% 0.16/0.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.16/0.43         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.16/0.43           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.16/0.43      inference('sup+', [status(thm)], ['4', '5'])).
% 0.16/0.43  thf('7', plain,
% 0.16/0.43      (![X0 : $i, X1 : $i]:
% 0.16/0.43         ((k1_enumset1 @ X1 @ X1 @ X0)
% 0.16/0.43           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.16/0.43      inference('sup+', [status(thm)], ['3', '6'])).
% 0.16/0.43  thf('8', plain,
% 0.16/0.43      (![X10 : $i, X11 : $i]:
% 0.16/0.43         ((k1_enumset1 @ X10 @ X10 @ X11) = (k2_tarski @ X10 @ X11))),
% 0.16/0.43      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.16/0.43  thf(t69_enumset1, axiom,
% 0.16/0.43    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.16/0.43  thf('9', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.16/0.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.16/0.43  thf('10', plain,
% 0.16/0.43      (![X0 : $i, X1 : $i]:
% 0.16/0.43         ((k2_tarski @ X1 @ X0)
% 0.16/0.43           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.16/0.43      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.16/0.43  thf('11', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.16/0.43      inference('demod', [status(thm)], ['0', '10'])).
% 0.16/0.43  thf('12', plain, ($false), inference('simplify', [status(thm)], ['11'])).
% 0.16/0.43  
% 0.16/0.43  % SZS output end Refutation
% 0.16/0.43  
% 0.16/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
