%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iHz8SXxc4x

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:57 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   27 (  35 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  184 ( 250 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t31_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X3 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['3','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iHz8SXxc4x
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:36:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.04/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.24  % Solved by: fo/fo7.sh
% 1.04/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.24  % done 542 iterations in 0.748s
% 1.04/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.24  % SZS output start Refutation
% 1.04/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.04/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.04/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.24  thf(t31_xboole_1, conjecture,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( r1_tarski @
% 1.04/1.24       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 1.04/1.24       ( k2_xboole_0 @ B @ C ) ))).
% 1.04/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.24    (~( ![A:$i,B:$i,C:$i]:
% 1.04/1.24        ( r1_tarski @
% 1.04/1.24          ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 1.04/1.24          ( k2_xboole_0 @ B @ C ) ) )),
% 1.04/1.24    inference('cnf.neg', [status(esa)], [t31_xboole_1])).
% 1.04/1.24  thf('0', plain,
% 1.04/1.24      (~ (r1_tarski @ 
% 1.04/1.24          (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 1.04/1.24           (k3_xboole_0 @ sk_A @ sk_C)) @ 
% 1.04/1.24          (k2_xboole_0 @ sk_B @ sk_C))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(commutativity_k3_xboole_0, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.04/1.24  thf('1', plain,
% 1.04/1.24      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf('2', plain,
% 1.04/1.24      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.04/1.24  thf('3', plain,
% 1.04/1.24      (~ (r1_tarski @ 
% 1.04/1.24          (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.04/1.24           (k3_xboole_0 @ sk_C @ sk_A)) @ 
% 1.04/1.24          (k2_xboole_0 @ sk_B @ sk_C))),
% 1.04/1.24      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.04/1.24  thf(commutativity_k2_xboole_0, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.04/1.24  thf('4', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.04/1.24      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.04/1.24  thf(t24_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 1.04/1.24       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 1.04/1.24  thf('5', plain,
% 1.04/1.24      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.04/1.24         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11))
% 1.04/1.24           = (k3_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ (k2_xboole_0 @ X9 @ X11)))),
% 1.04/1.24      inference('cnf', [status(esa)], [t24_xboole_1])).
% 1.04/1.24  thf(t17_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.04/1.24  thf('6', plain,
% 1.04/1.24      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 1.04/1.24      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.04/1.24  thf('7', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (r1_tarski @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.04/1.24          (k2_xboole_0 @ X2 @ X1))),
% 1.04/1.24      inference('sup+', [status(thm)], ['5', '6'])).
% 1.04/1.24  thf('8', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 1.04/1.24          (k2_xboole_0 @ X0 @ X2))),
% 1.04/1.24      inference('sup+', [status(thm)], ['4', '7'])).
% 1.04/1.24  thf('9', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.24         (r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 1.04/1.24          (k2_xboole_0 @ X0 @ X2))),
% 1.04/1.24      inference('sup+', [status(thm)], ['4', '7'])).
% 1.04/1.24  thf(t1_xboole_1, axiom,
% 1.04/1.24    (![A:$i,B:$i,C:$i]:
% 1.04/1.24     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.04/1.24       ( r1_tarski @ A @ C ) ))).
% 1.04/1.24  thf('10', plain,
% 1.04/1.24      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.04/1.24         (~ (r1_tarski @ X6 @ X7)
% 1.04/1.24          | ~ (r1_tarski @ X7 @ X8)
% 1.04/1.24          | (r1_tarski @ X6 @ X8))),
% 1.04/1.24      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.04/1.24  thf('11', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.24         ((r1_tarski @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X3)
% 1.04/1.24          | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X3))),
% 1.04/1.24      inference('sup-', [status(thm)], ['9', '10'])).
% 1.04/1.24  thf('12', plain,
% 1.04/1.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.24         (r1_tarski @ 
% 1.04/1.24          (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X3) @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.04/1.24          (k2_xboole_0 @ X1 @ X0))),
% 1.04/1.24      inference('sup-', [status(thm)], ['8', '11'])).
% 1.04/1.24  thf('13', plain, ($false), inference('demod', [status(thm)], ['3', '12'])).
% 1.04/1.24  
% 1.04/1.24  % SZS output end Refutation
% 1.04/1.24  
% 1.04/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
