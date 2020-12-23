%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SwzucZLEQc

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:14 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  166 ( 190 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t75_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t75_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
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
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('11',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SwzucZLEQc
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 684 iterations in 0.175s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(t75_xboole_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.64          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i]:
% 0.45/0.64        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.64             ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t75_xboole_1])).
% 0.45/0.64  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.64  thf('2', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t51_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.45/0.64       ( A ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X8 : $i, X9 : $i]:
% 0.45/0.64         ((k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X8 @ X9))
% 0.45/0.64           = (X8))),
% 0.45/0.64      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.45/0.64  thf(t70_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.45/0.64       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.45/0.64            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X10 @ X11)
% 0.45/0.64          | ~ (r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.64         (~ (r1_xboole_0 @ X2 @ X0)
% 0.45/0.64          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['2', '5'])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['1', '6'])).
% 0.45/0.64  thf(d7_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.64       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X2 : $i, X3 : $i]:
% 0.45/0.64         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.45/0.64           (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.64  thf('10', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.45/0.64      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.64  thf('11', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('sup+', [status(thm)], ['9', '10'])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X2 : $i, X4 : $i]:
% 0.45/0.64         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.45/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.64  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
