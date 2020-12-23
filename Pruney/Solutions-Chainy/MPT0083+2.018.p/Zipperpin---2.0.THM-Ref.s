%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bksxVqySJa

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  29 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  121 ( 162 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( r1_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( r1_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['3','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bksxVqySJa
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 43 iterations in 0.022s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(t76_xboole_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.50       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.50          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.20/0.50          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.20/0.50          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.20/0.50  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.50  thf('6', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(t74_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.50          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X4 @ X5)
% 0.20/0.50          | (r1_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X4 @ X5)
% 0.20/0.50          | (r1_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ($false), inference('demod', [status(thm)], ['3', '12'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
