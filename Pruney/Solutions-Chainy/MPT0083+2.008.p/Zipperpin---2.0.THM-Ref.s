%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hWRV9XFWmb

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:16 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 353 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
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
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
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
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ( r1_xboole_0 @ X21 @ X24 )
      | ~ ( r1_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['3','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hWRV9XFWmb
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:48:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 1588 iterations in 0.521s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(t76_xboole_1, conjecture,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( r1_xboole_0 @ A @ B ) =>
% 0.75/0.97       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.97        ( ( r1_xboole_0 @ A @ B ) =>
% 0.75/0.97          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.75/0.97  thf('0', plain,
% 0.75/0.97      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ 
% 0.75/0.97          (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('2', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('3', plain,
% 0.75/0.97      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.75/0.97          (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.75/0.97      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.75/0.97  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(d7_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.97       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.97  thf('5', plain,
% 0.75/0.97      (![X2 : $i, X3 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.75/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.97  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.97  thf('7', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('8', plain,
% 0.75/0.97      (![X2 : $i, X4 : $i]:
% 0.75/0.97         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.97  thf('9', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.97  thf('10', plain,
% 0.75/0.97      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['6', '9'])).
% 0.75/0.97  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.75/0.97      inference('simplify', [status(thm)], ['10'])).
% 0.75/0.97  thf(t22_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.75/0.97  thf('12', plain,
% 0.75/0.97      (![X9 : $i, X10 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 0.75/0.97      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.75/0.97  thf(t70_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.75/0.97            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.75/0.97       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.75/0.97            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.75/0.97  thf('13', plain,
% 0.75/0.97      (![X21 : $i, X22 : $i, X24 : $i]:
% 0.75/0.97         ((r1_xboole_0 @ X21 @ X24)
% 0.75/0.97          | ~ (r1_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X24)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.75/0.97  thf('14', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         (~ (r1_xboole_0 @ X2 @ X0)
% 0.75/0.97          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.97  thf('15', plain,
% 0.75/0.97      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['11', '14'])).
% 0.75/0.97  thf(t4_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.75/0.97            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.75/0.97  thf('16', plain,
% 0.75/0.97      (![X5 : $i, X6 : $i]:
% 0.75/0.97         ((r1_xboole_0 @ X5 @ X6)
% 0.75/0.97          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.75/0.97  thf('17', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('18', plain,
% 0.75/0.97      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.75/0.97          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.75/0.97      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.75/0.97  thf('19', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.97          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['17', '18'])).
% 0.75/0.97  thf('20', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['16', '19'])).
% 0.75/0.97  thf('21', plain,
% 0.75/0.97      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.75/0.97      inference('sup-', [status(thm)], ['15', '20'])).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         (~ (r1_xboole_0 @ X2 @ X0)
% 0.75/0.97          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.97  thf('24', plain, ($false), inference('demod', [status(thm)], ['3', '23'])).
% 0.75/0.97  
% 0.75/0.97  % SZS output end Refutation
% 0.75/0.97  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
