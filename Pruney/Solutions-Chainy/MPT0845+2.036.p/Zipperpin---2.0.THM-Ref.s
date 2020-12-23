%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Ge7sTAoqj

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  73 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  340 ( 611 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ ( sk_C_2 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('4',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_A )
      | ~ ( r1_xboole_0 @ X21 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( sk_D @ X1 @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A )
      | ( X1
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A )
      | ( X1
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('14',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_A )
      | ~ ( r1_xboole_0 @ X21 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_D @ sk_A @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A )
      | ( sk_A
        = ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( sk_C_2 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_A )
      | ~ ( r1_xboole_0 @ X21 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( sk_C_2 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_2 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['23','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Ge7sTAoqj
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 88 iterations in 0.046s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(t3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf(t7_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( r2_hidden @ A @ B ) & 
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.49                 ( ![D:$i]:
% 0.20/0.49                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X18 @ X19) | (r2_hidden @ (sk_C_2 @ X19) @ X19))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(d5_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.49         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.20/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf(t1_mcart_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49             ( ![B:$i]:
% 0.20/0.49               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X21 : $i]: (~ (r2_hidden @ X21 @ sk_A) | ~ (r1_xboole_0 @ X21 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ X1)
% 0.20/0.49          | ((X1) = (k4_xboole_0 @ sk_A @ X0))
% 0.20/0.49          | ~ (r1_xboole_0 @ (sk_D @ X1 @ X0 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)
% 0.20/0.49          | ((X1) = (k4_xboole_0 @ sk_A @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf(t4_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.20/0.49          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.49  thf('10', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.49  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_C_2 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)
% 0.20/0.49          | ((X1) = (k4_xboole_0 @ sk_A @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X1 @ X0 @ sk_A) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X21 : $i]: (~ (r2_hidden @ X21 @ sk_A) | ~ (r1_xboole_0 @ X21 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_A) = (k4_xboole_0 @ sk_A @ X0))
% 0.20/0.49          | (r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)
% 0.20/0.49          | ~ (r1_xboole_0 @ (sk_D @ sk_A @ X0 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)
% 0.20/0.49          | ((sk_A) = (k4_xboole_0 @ sk_A @ X0)))),
% 0.20/0.49      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((sk_A) = (k1_xboole_0))
% 0.20/0.49        | (r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)
% 0.20/0.49        | (r2_hidden @ (sk_C_2 @ sk_A) @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['12', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((r2_hidden @ (sk_C_2 @ sk_A) @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((r2_hidden @ (sk_C_2 @ sk_A) @ sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X21 : $i]: (~ (r2_hidden @ X21 @ sk_A) | ~ (r1_xboole_0 @ X21 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, (~ (r1_xboole_0 @ (sk_C_2 @ sk_A) @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X18 @ X19)
% 0.20/0.49          | ~ (r2_hidden @ X20 @ X19)
% 0.20/0.49          | ~ (r2_hidden @ X20 @ (sk_C_2 @ X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (sk_C_2 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.49      inference('condensation', [status(thm)], ['26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X1)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_2 @ X0)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X0)
% 0.20/0.49          | (r1_xboole_0 @ (sk_C_2 @ X0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '28'])).
% 0.20/0.49  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_2 @ X0) @ X0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.49  thf('31', plain, ($false), inference('demod', [status(thm)], ['23', '30'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
