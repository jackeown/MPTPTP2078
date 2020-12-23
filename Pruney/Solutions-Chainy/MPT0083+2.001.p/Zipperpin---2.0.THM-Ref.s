%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bV5RL2sV6f

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:15 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  242 ( 388 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['10'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['3','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bV5RL2sV6f
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:21:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.72/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.91  % Solved by: fo/fo7.sh
% 0.72/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.91  % done 1132 iterations in 0.458s
% 0.72/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.91  % SZS output start Refutation
% 0.72/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.72/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.91  thf(t76_xboole_1, conjecture,
% 0.72/0.91    (![A:$i,B:$i,C:$i]:
% 0.72/0.91     ( ( r1_xboole_0 @ A @ B ) =>
% 0.72/0.91       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.72/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.91        ( ( r1_xboole_0 @ A @ B ) =>
% 0.72/0.91          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.72/0.91    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.72/0.91  thf('0', plain,
% 0.72/0.91      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.72/0.91          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf(commutativity_k3_xboole_0, axiom,
% 0.72/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.72/0.91  thf('1', plain,
% 0.72/0.91      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('2', plain,
% 0.72/0.91      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('3', plain,
% 0.72/0.91      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.72/0.91          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.72/0.91      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.72/0.91  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf(d7_xboole_0, axiom,
% 0.72/0.91    (![A:$i,B:$i]:
% 0.72/0.91     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.72/0.91       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.72/0.91  thf('5', plain,
% 0.72/0.91      (![X4 : $i, X5 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.72/0.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.91  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.91  thf('7', plain,
% 0.72/0.91      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.72/0.91  thf('8', plain,
% 0.72/0.91      (![X4 : $i, X6 : $i]:
% 0.72/0.91         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.72/0.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.91  thf('9', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.72/0.91  thf('10', plain,
% 0.72/0.91      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.72/0.91      inference('sup-', [status(thm)], ['6', '9'])).
% 0.72/0.91  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.72/0.91      inference('simplify', [status(thm)], ['10'])).
% 0.72/0.91  thf(t22_xboole_1, axiom,
% 0.72/0.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.72/0.91  thf('12', plain,
% 0.72/0.91      (![X7 : $i, X8 : $i]:
% 0.72/0.91         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.72/0.91      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.72/0.91  thf(commutativity_k2_xboole_0, axiom,
% 0.72/0.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.72/0.91  thf('13', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.72/0.91  thf(t70_xboole_1, axiom,
% 0.72/0.91    (![A:$i,B:$i,C:$i]:
% 0.72/0.91     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.72/0.91            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.72/0.91       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.72/0.91            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.72/0.91  thf('14', plain,
% 0.72/0.91      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.72/0.91         ((r1_xboole_0 @ X19 @ X20)
% 0.72/0.91          | ~ (r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X22)))),
% 0.72/0.91      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.72/0.91  thf('15', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.72/0.91          | (r1_xboole_0 @ X2 @ X0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['13', '14'])).
% 0.72/0.91  thf('16', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (~ (r1_xboole_0 @ X2 @ X0)
% 0.72/0.91          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.72/0.91      inference('sup-', [status(thm)], ['12', '15'])).
% 0.72/0.91  thf('17', plain,
% 0.72/0.91      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['11', '16'])).
% 0.72/0.91  thf('18', plain,
% 0.72/0.91      (![X4 : $i, X5 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.72/0.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.72/0.91  thf('19', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['17', '18'])).
% 0.72/0.91  thf('20', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.72/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.72/0.91  thf('21', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         (((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.91          | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.72/0.91      inference('sup-', [status(thm)], ['19', '20'])).
% 0.72/0.91  thf('22', plain,
% 0.72/0.91      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.72/0.91      inference('simplify', [status(thm)], ['21'])).
% 0.72/0.91  thf('23', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.91         (~ (r1_xboole_0 @ X2 @ X0)
% 0.72/0.91          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.72/0.91      inference('sup-', [status(thm)], ['12', '15'])).
% 0.72/0.91  thf('24', plain,
% 0.72/0.91      (![X0 : $i, X1 : $i]:
% 0.72/0.91         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))),
% 0.72/0.91      inference('sup-', [status(thm)], ['22', '23'])).
% 0.72/0.91  thf('25', plain, ($false), inference('demod', [status(thm)], ['3', '24'])).
% 0.72/0.91  
% 0.72/0.91  % SZS output end Refutation
% 0.72/0.91  
% 0.72/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
