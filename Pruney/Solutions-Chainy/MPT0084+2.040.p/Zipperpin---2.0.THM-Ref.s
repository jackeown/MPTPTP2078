%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SHgYOe6mgV

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:24 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   15 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  321 ( 539 expanded)
%              Number of equality atoms :   33 (  52 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k3_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k3_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SHgYOe6mgV
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 231 iterations in 0.125s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(t77_xboole_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.38/0.58          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.58        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.38/0.58             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.38/0.58  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(d7_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('4', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(l32_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X3 : $i, X5 : $i]:
% 0.38/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf(t48_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.38/0.58           = (k3_xboole_0 @ X20 @ X21))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.58  thf(t3_boole, axiom,
% 0.38/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.58  thf('9', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.58  thf('10', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.58  thf(t16_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.58       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8)
% 0.38/0.58           = (k3_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ sk_A @ X0)
% 0.38/0.58           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.38/0.58          | (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58        | (r1_xboole_0 @ sk_A @ 
% 0.38/0.58           (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['3', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.38/0.58           = (k3_xboole_0 @ X20 @ X21))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf(t36_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.38/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X3 : $i, X5 : $i]:
% 0.38/0.58         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['17', '20'])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.38/0.58           = (k3_xboole_0 @ X20 @ X21))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.38/0.58           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.58  thf('24', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8)
% 0.38/0.58           = (k3_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ X0 @ X1)
% 0.38/0.58           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.38/0.58  thf('27', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))),
% 0.38/0.58      inference('demod', [status(thm)], ['16', '26'])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k3_xboole_0 @ sk_A @ X0)
% 0.38/0.58           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.38/0.58  thf('31', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i]:
% 0.38/0.58         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.38/0.58  thf('34', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.38/0.58      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.58  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
