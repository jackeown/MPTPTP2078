%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4kdoxOXxO

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  190 ( 236 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t109_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ D @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ D @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t109_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C ) ),
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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4kdoxOXxO
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 12 iterations in 0.015s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t109_enumset1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ D @ C ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ D @ C ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t109_enumset1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.46         != (k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(commutativity_k2_tarski, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.46  thf(l53_enumset1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.46       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.21/0.46           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2)
% 0.21/0.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.21/0.46           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.21/0.46           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1)
% 0.21/0.46           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.21/0.46           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.46         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.46      inference('demod', [status(thm)], ['6', '11'])).
% 0.21/0.46  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
