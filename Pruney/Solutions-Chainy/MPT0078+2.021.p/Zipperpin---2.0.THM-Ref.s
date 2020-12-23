%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T6lzUytMS6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:55 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   56 (  94 expanded)
%              Number of leaves         :   20 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 ( 658 expanded)
%              Number of equality atoms :   43 (  85 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('24',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['22','23','30'])).

thf('32',plain,(
    sk_A = sk_C_1 ),
    inference('sup+',[status(thm)],['10','31'])).

thf('33',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T6lzUytMS6
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 478 iterations in 0.289s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.73  thf(t71_xboole_1, conjecture,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.51/0.73         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.51/0.73       ( ( A ) = ( C ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.73        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.51/0.73            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.51/0.73          ( ( A ) = ( C ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.51/0.73  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(t7_xboole_0, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.51/0.73          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.51/0.73      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.73  thf(t4_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.73            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.51/0.73  thf('2', plain,
% 0.51/0.73      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.51/0.73          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.73  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['0', '3'])).
% 0.51/0.73  thf(t51_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.51/0.73       ( A ) ))).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (![X20 : $i, X21 : $i]:
% 0.51/0.73         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.73           = (X20))),
% 0.51/0.73      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.51/0.73  thf('6', plain,
% 0.51/0.73      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))),
% 0.51/0.73      inference('sup+', [status(thm)], ['4', '5'])).
% 0.51/0.73  thf(commutativity_k2_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.51/0.73  thf('7', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.73  thf(t1_boole, axiom,
% 0.51/0.73    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.73  thf('8', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.51/0.73      inference('cnf', [status(esa)], [t1_boole])).
% 0.51/0.73  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.51/0.73  thf('10', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['6', '9'])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(t3_boole, axiom,
% 0.51/0.73    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.73  thf('12', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.51/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.51/0.73  thf(t48_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('13', plain,
% 0.51/0.73      (![X18 : $i, X19 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.51/0.73           = (k3_xboole_0 @ X18 @ X19))),
% 0.51/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['12', '13'])).
% 0.51/0.73  thf(t2_boole, axiom,
% 0.51/0.73    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.51/0.73  thf('15', plain,
% 0.51/0.73      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.73      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.73  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.51/0.73      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.73  thf(t42_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.73       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.51/0.73  thf('17', plain,
% 0.51/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X17) @ X16)
% 0.51/0.73           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ 
% 0.51/0.73              (k4_xboole_0 @ X17 @ X16)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.51/0.73  thf('18', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.51/0.73           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.51/0.73  thf('19', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.73  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.51/0.73           = (k4_xboole_0 @ X1 @ X0))),
% 0.51/0.73      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.51/0.73  thf('22', plain,
% 0.51/0.73      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.51/0.73         = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['11', '21'])).
% 0.51/0.73  thf('23', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.51/0.73           = (k4_xboole_0 @ X1 @ X0))),
% 0.51/0.73      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.51/0.73  thf('24', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.73  thf('26', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.73  thf('27', plain,
% 0.51/0.73      (![X20 : $i, X21 : $i]:
% 0.51/0.73         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.51/0.73           = (X20))),
% 0.51/0.73      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 0.51/0.73         = (sk_C_1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['26', '27'])).
% 0.51/0.73  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['7', '8'])).
% 0.51/0.73  thf('30', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['28', '29'])).
% 0.51/0.73  thf('31', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_C_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['22', '23', '30'])).
% 0.51/0.73  thf('32', plain, (((sk_A) = (sk_C_1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['10', '31'])).
% 0.51/0.73  thf('33', plain, (((sk_A) != (sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('34', plain, ($false),
% 0.51/0.73      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
