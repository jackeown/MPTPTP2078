%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dbAhPdBpQs

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:16 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  220 ( 344 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
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
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X17 )
      | ~ ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
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

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['3','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dbAhPdBpQs
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 1075 iterations in 0.372s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.82  thf(t76_xboole_1, conjecture,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( r1_xboole_0 @ A @ B ) =>
% 0.59/0.82       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.82        ( ( r1_xboole_0 @ A @ B ) =>
% 0.59/0.82          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.59/0.82  thf('0', plain,
% 0.59/0.82      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.59/0.82          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.82  thf('1', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.82  thf('2', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.82  thf('3', plain,
% 0.59/0.82      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.59/0.82          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.59/0.82      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.59/0.82  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(d7_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.82       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (![X2 : $i, X3 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.59/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.82  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.82  thf('7', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.82  thf('8', plain,
% 0.59/0.82      (![X2 : $i, X4 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.59/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.82  thf('9', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.82  thf('10', plain,
% 0.59/0.82      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['6', '9'])).
% 0.59/0.82  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.59/0.82      inference('simplify', [status(thm)], ['10'])).
% 0.59/0.82  thf(t22_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (![X5 : $i, X6 : $i]:
% 0.59/0.82         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.59/0.82      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.59/0.82  thf(t70_xboole_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.59/0.82            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.59/0.82       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.59/0.82            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.59/0.82  thf('13', plain,
% 0.59/0.82      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X14 @ X17)
% 0.59/0.82          | ~ (r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X17)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.59/0.82  thf('14', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         (~ (r1_xboole_0 @ X2 @ X0)
% 0.59/0.82          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.82  thf('15', plain,
% 0.59/0.82      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['11', '14'])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (![X2 : $i, X3 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.59/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.82  thf('17', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.82  thf('18', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.82  thf('19', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.82          | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.82  thf('20', plain,
% 0.59/0.82      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.59/0.82      inference('simplify', [status(thm)], ['19'])).
% 0.59/0.82  thf('21', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         (~ (r1_xboole_0 @ X2 @ X0)
% 0.59/0.82          | (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.82  thf('22', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.82  thf('23', plain, ($false), inference('demod', [status(thm)], ['3', '22'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.59/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
