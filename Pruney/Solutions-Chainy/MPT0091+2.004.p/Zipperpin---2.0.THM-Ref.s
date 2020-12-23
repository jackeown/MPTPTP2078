%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4kygg07Qg

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:43 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 133 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  436 (1570 expanded)
%              Number of equality atoms :   21 (  86 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t84_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ A @ C )
        & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C )
          & ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('14',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_C_1 ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('32',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q4kygg07Qg
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.01/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.20  % Solved by: fo/fo7.sh
% 1.01/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.20  % done 1714 iterations in 0.751s
% 1.01/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.20  % SZS output start Refutation
% 1.01/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.20  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.01/1.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.01/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.01/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.01/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.01/1.20  thf(t84_xboole_1, conjecture,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 1.01/1.20          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ))).
% 1.01/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.20    (~( ![A:$i,B:$i,C:$i]:
% 1.01/1.20        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ C ) & 
% 1.01/1.20             ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) )),
% 1.01/1.20    inference('cnf.neg', [status(esa)], [t84_xboole_1])).
% 1.01/1.20  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(t3_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.01/1.20            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.01/1.20       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.01/1.20            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.01/1.20  thf('1', plain,
% 1.01/1.20      (![X6 : $i, X7 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 1.01/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.01/1.20  thf(d5_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.01/1.20       ( ![D:$i]:
% 1.01/1.20         ( ( r2_hidden @ D @ C ) <=>
% 1.01/1.20           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.01/1.20  thf('2', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X0 @ X1)
% 1.01/1.20          | (r2_hidden @ X0 @ X2)
% 1.01/1.20          | (r2_hidden @ X0 @ X3)
% 1.01/1.20          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.01/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.01/1.20  thf('3', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.01/1.20          | (r2_hidden @ X0 @ X2)
% 1.01/1.20          | ~ (r2_hidden @ X0 @ X1))),
% 1.01/1.20      inference('simplify', [status(thm)], ['2'])).
% 1.01/1.20  thf('4', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X1 @ X0)
% 1.01/1.20          | (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 1.01/1.20          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['1', '3'])).
% 1.01/1.20  thf('5', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('6', plain,
% 1.01/1.20      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.01/1.20         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.01/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.01/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.01/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.01/1.20  thf('7', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.01/1.20          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.01/1.20      inference('eq_fact', [status(thm)], ['6'])).
% 1.01/1.20  thf('8', plain,
% 1.01/1.20      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.01/1.20         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.01/1.20          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.01/1.20          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.01/1.20          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.01/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.01/1.20  thf('9', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.01/1.20          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.01/1.20          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.01/1.20          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('10', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.01/1.20          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.01/1.20          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.01/1.20      inference('simplify', [status(thm)], ['9'])).
% 1.01/1.20  thf('11', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.01/1.20          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.01/1.20      inference('eq_fact', [status(thm)], ['6'])).
% 1.01/1.20  thf('12', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.01/1.20          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.01/1.20      inference('clc', [status(thm)], ['10', '11'])).
% 1.01/1.20  thf('13', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.01/1.20          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.01/1.20      inference('eq_fact', [status(thm)], ['6'])).
% 1.01/1.20  thf('14', plain,
% 1.01/1.20      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X8 @ X6)
% 1.01/1.20          | ~ (r2_hidden @ X8 @ X9)
% 1.01/1.20          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.01/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.01/1.20  thf('15', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.01/1.20          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.01/1.20          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 1.01/1.20      inference('sup-', [status(thm)], ['13', '14'])).
% 1.01/1.20  thf('16', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 1.01/1.20          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.01/1.20          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['12', '15'])).
% 1.01/1.20  thf('17', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 1.01/1.20      inference('simplify', [status(thm)], ['16'])).
% 1.01/1.20  thf('18', plain,
% 1.01/1.20      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['5', '17'])).
% 1.01/1.20  thf('19', plain,
% 1.01/1.20      (![X6 : $i, X7 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 1.01/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.01/1.20  thf('20', plain,
% 1.01/1.20      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X4 @ X3)
% 1.01/1.20          | ~ (r2_hidden @ X4 @ X2)
% 1.01/1.20          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.01/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.01/1.20  thf('21', plain,
% 1.01/1.20      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X4 @ X2)
% 1.01/1.20          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.01/1.20      inference('simplify', [status(thm)], ['20'])).
% 1.01/1.20  thf('22', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.01/1.20          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['19', '21'])).
% 1.01/1.20  thf('23', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 1.01/1.20          | (r1_xboole_0 @ 
% 1.01/1.20             (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['18', '22'])).
% 1.01/1.20  thf('24', plain,
% 1.01/1.20      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['5', '17'])).
% 1.01/1.20  thf('25', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 1.01/1.20          | (r1_xboole_0 @ sk_A @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['23', '24'])).
% 1.01/1.20  thf('26', plain,
% 1.01/1.20      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_C_1)
% 1.01/1.20        | (r1_xboole_0 @ sk_A @ sk_B)
% 1.01/1.20        | (r1_xboole_0 @ sk_A @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['4', '25'])).
% 1.01/1.20  thf('27', plain,
% 1.01/1.20      (((r1_xboole_0 @ sk_A @ sk_B)
% 1.01/1.20        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_C_1))),
% 1.01/1.20      inference('simplify', [status(thm)], ['26'])).
% 1.01/1.20  thf('28', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('29', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_C_1)),
% 1.01/1.20      inference('clc', [status(thm)], ['27', '28'])).
% 1.01/1.20  thf('30', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('31', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 1.01/1.20      inference('simplify', [status(thm)], ['16'])).
% 1.01/1.20  thf('32', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.01/1.20      inference('sup-', [status(thm)], ['30', '31'])).
% 1.01/1.20  thf('33', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.01/1.20          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['19', '21'])).
% 1.01/1.20  thf('34', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1)
% 1.01/1.20          | (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['32', '33'])).
% 1.01/1.20  thf('35', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.01/1.20      inference('sup-', [status(thm)], ['30', '31'])).
% 1.01/1.20  thf('36', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1)
% 1.01/1.20          | (r1_xboole_0 @ sk_A @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['34', '35'])).
% 1.01/1.20  thf('37', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 1.01/1.20      inference('sup-', [status(thm)], ['29', '36'])).
% 1.01/1.20  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 1.01/1.20  
% 1.01/1.20  % SZS output end Refutation
% 1.01/1.20  
% 1.01/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
