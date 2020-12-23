%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mVD7Gk8fpS

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:41 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   51 (  82 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  289 ( 591 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14 = X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X14 ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ B @ C ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('1',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_3 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_C_3 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['23','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mVD7Gk8fpS
% 0.17/0.38  % Computer   : n010.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 11:05:30 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.52  % Solved by: fo/fo7.sh
% 0.25/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.52  % done 42 iterations in 0.028s
% 0.25/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.52  % SZS output start Refutation
% 0.25/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.25/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.25/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.52  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.25/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.52  thf(t2_tarski, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.25/0.52       ( ( A ) = ( B ) ) ))).
% 0.25/0.52  thf('0', plain,
% 0.25/0.52      (![X13 : $i, X14 : $i]:
% 0.25/0.52         (((X14) = (X13))
% 0.25/0.52          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ X13)
% 0.25/0.52          | (r2_hidden @ (sk_C_1 @ X13 @ X14) @ X14))),
% 0.25/0.52      inference('cnf', [status(esa)], [t2_tarski])).
% 0.25/0.52  thf(t67_xboole_1, conjecture,
% 0.25/0.52    (![A:$i,B:$i,C:$i]:
% 0.25/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.25/0.52         ( r1_xboole_0 @ B @ C ) ) =>
% 0.25/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.52        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.25/0.52            ( r1_xboole_0 @ B @ C ) ) =>
% 0.25/0.52          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.25/0.52    inference('cnf.neg', [status(esa)], [t67_xboole_1])).
% 0.25/0.52  thf('1', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(d7_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.25/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.52  thf('2', plain,
% 0.25/0.52      (![X10 : $i, X11 : $i]:
% 0.25/0.52         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.25/0.52          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.25/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.25/0.52  thf('3', plain, (((k3_xboole_0 @ sk_B @ sk_C_3) = (k1_xboole_0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.52  thf(t4_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.25/0.52  thf('4', plain,
% 0.25/0.52      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X17 @ (k3_xboole_0 @ X15 @ X18))
% 0.25/0.52          | ~ (r1_xboole_0 @ X15 @ X18))),
% 0.25/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.25/0.52  thf('5', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.25/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.52  thf('6', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.25/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.25/0.52  thf('8', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.25/0.52          | ((X0) = (k1_xboole_0)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['0', '7'])).
% 0.25/0.52  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(d3_tarski, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.52  thf('10', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.52          | (r2_hidden @ X0 @ X2)
% 0.25/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.52  thf('11', plain,
% 0.25/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.25/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.25/0.52  thf('12', plain,
% 0.25/0.52      ((((sk_A) = (k1_xboole_0))
% 0.25/0.52        | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_B))),
% 0.25/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.25/0.52  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('14', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_B)),
% 0.25/0.52      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.25/0.52  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_C_3) = (k1_xboole_0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.52  thf(t47_xboole_1, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.25/0.52  thf('16', plain,
% 0.25/0.52      (![X20 : $i, X21 : $i]:
% 0.25/0.52         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.25/0.52           = (k4_xboole_0 @ X20 @ X21))),
% 0.25/0.52      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.25/0.52  thf('17', plain,
% 0.25/0.52      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C_3))),
% 0.25/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.25/0.52  thf(t3_boole, axiom,
% 0.25/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.25/0.52  thf('18', plain, (![X19 : $i]: ((k4_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.25/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.25/0.52  thf('19', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C_3))),
% 0.25/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.25/0.52  thf(d5_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i,C:$i]:
% 0.25/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.25/0.53       ( ![D:$i]:
% 0.25/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.25/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.25/0.53  thf('20', plain,
% 0.25/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.53         (~ (r2_hidden @ X8 @ X7)
% 0.25/0.53          | ~ (r2_hidden @ X8 @ X6)
% 0.25/0.53          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.25/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.25/0.53  thf('21', plain,
% 0.25/0.53      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.25/0.53         (~ (r2_hidden @ X8 @ X6)
% 0.25/0.53          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.25/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.25/0.53  thf('22', plain,
% 0.25/0.53      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.25/0.53      inference('sup-', [status(thm)], ['19', '21'])).
% 0.25/0.53  thf('23', plain, (~ (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_C_3)),
% 0.25/0.53      inference('sup-', [status(thm)], ['14', '22'])).
% 0.25/0.53  thf('24', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.25/0.53          | ((X0) = (k1_xboole_0)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['0', '7'])).
% 0.25/0.53  thf('25', plain, ((r1_tarski @ sk_A @ sk_C_3)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('26', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.53          | (r2_hidden @ X0 @ X2)
% 0.25/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.53  thf('27', plain,
% 0.25/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_3) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.25/0.53  thf('28', plain,
% 0.25/0.53      ((((sk_A) = (k1_xboole_0))
% 0.25/0.53        | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_C_3))),
% 0.25/0.53      inference('sup-', [status(thm)], ['24', '27'])).
% 0.25/0.53  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('30', plain, ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_C_3)),
% 0.25/0.53      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.25/0.53  thf('31', plain, ($false), inference('demod', [status(thm)], ['23', '30'])).
% 0.25/0.53  
% 0.25/0.53  % SZS output end Refutation
% 0.25/0.53  
% 0.25/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
