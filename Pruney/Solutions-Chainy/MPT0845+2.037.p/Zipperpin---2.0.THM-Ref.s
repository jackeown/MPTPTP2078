%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8nf4ZY3A6N

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 588 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

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

thf('2',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( r1_xboole_0 @ X18 @ sk_A ) ) ),
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_A )
      | ~ ( r1_xboole_0 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X17 @ ( sk_C_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X18: $i] :
      ~ ( r2_hidden @ X18 @ sk_A ) ),
    inference(demod,[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X18: $i] :
      ~ ( r2_hidden @ X18 @ sk_A ) ),
    inference(demod,[status(thm)],['2','15'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup+',[status(thm)],['17','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8nf4ZY3A6N
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 65 iterations in 0.041s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(d5_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.49         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.21/0.49          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.49      inference('eq_fact', [status(thm)], ['0'])).
% 0.21/0.49  thf(t1_mcart_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49             ( ![B:$i]:
% 0.21/0.49               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X18 : $i]: (~ (r2_hidden @ X18 @ sk_A) | ~ (r1_xboole_0 @ X18 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf(t7_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.49                 ( ![D:$i]:
% 0.21/0.49                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X15 @ X16) | (r2_hidden @ (sk_C_1 @ X16) @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X18 : $i]: (~ (r2_hidden @ X18 @ sk_A) | ~ (r1_xboole_0 @ X18 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X15 @ X16)
% 0.21/0.49          | ~ (r2_hidden @ X17 @ X16)
% 0.21/0.49          | ~ (r2_hidden @ X17 @ (sk_C_1 @ X16)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.49      inference('condensation', [status(thm)], ['10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.21/0.49          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '12'])).
% 0.21/0.49  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '14'])).
% 0.21/0.49  thf('16', plain, (![X18 : $i]: ~ (r2_hidden @ X18 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '15'])).
% 0.21/0.49  thf('17', plain, (![X0 : $i]: ((sk_A) = (k4_xboole_0 @ sk_A @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.49         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.49  thf(t113_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.21/0.49          | ((X12) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.49  thf(t152_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.49  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.49          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.49  thf('24', plain, (![X18 : $i]: ~ (r2_hidden @ X18 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '15'])).
% 0.21/0.49  thf('25', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['17', '25'])).
% 0.21/0.49  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
