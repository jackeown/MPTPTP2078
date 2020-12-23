%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D8BEVhIJJj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  235 ( 268 expanded)
%              Number of equality atoms :   25 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t78_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          = ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
 != ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['7','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D8BEVhIJJj
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.56  % Solved by: fo/fo7.sh
% 0.19/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.56  % done 164 iterations in 0.103s
% 0.19/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.56  % SZS output start Refutation
% 0.19/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.56  thf(t78_xboole_1, conjecture,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( r1_xboole_0 @ A @ B ) =>
% 0.19/0.56       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.19/0.56         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.19/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.56        ( ( r1_xboole_0 @ A @ B ) =>
% 0.36/0.56          ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.36/0.56            ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t78_xboole_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.36/0.56         != (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t7_xboole_0, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.56  thf(t4_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.36/0.56          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.56  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.56  thf(t51_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.36/0.56       ( A ) ))).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X15 : $i, X16 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.36/0.56           = (X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.36/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.56  thf(t1_boole, axiom,
% 0.36/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.56  thf('9', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.36/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.56  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('11', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['7', '10'])).
% 0.36/0.56  thf(t41_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.56       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.36/0.56           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.56  thf(t48_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.36/0.56           = (k3_xboole_0 @ X13 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.36/0.56           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.36/0.56           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['11', '14'])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.36/0.56           = (k3_xboole_0 @ X13 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k3_xboole_0 @ sk_A @ X0)
% 0.36/0.56           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ X0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (((k3_xboole_0 @ sk_A @ sk_C_1) != (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['0', '17'])).
% 0.36/0.56  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
