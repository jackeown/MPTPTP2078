%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rSXakH4V0S

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:37 EST 2020

% Result     : Theorem 10.77s
% Output     : Refutation 10.77s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  424 ( 733 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

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
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('11',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X13 != X12 )
      | ( r2_hidden @ X13 @ X14 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X12: $i] :
      ( r2_hidden @ X12 @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ X0 @ ( k1_tarski @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_A ) @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','33'])).

thf('35',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rSXakH4V0S
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.77/10.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.77/10.99  % Solved by: fo/fo7.sh
% 10.77/10.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.77/10.99  % done 10348 iterations in 10.537s
% 10.77/10.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.77/10.99  % SZS output start Refutation
% 10.77/10.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.77/10.99  thf(sk_A_type, type, sk_A: $i).
% 10.77/10.99  thf(sk_B_type, type, sk_B: $i).
% 10.77/10.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.77/10.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 10.77/10.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.77/10.99  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 10.77/10.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 10.77/10.99  thf(d4_xboole_0, axiom,
% 10.77/10.99    (![A:$i,B:$i,C:$i]:
% 10.77/10.99     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 10.77/10.99       ( ![D:$i]:
% 10.77/10.99         ( ( r2_hidden @ D @ C ) <=>
% 10.77/10.99           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 10.77/10.99  thf('0', plain,
% 10.77/10.99      (![X1 : $i, X2 : $i, X5 : $i]:
% 10.77/10.99         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 10.77/10.99          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 10.77/10.99          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 10.77/10.99      inference('cnf', [status(esa)], [d4_xboole_0])).
% 10.77/10.99  thf('1', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 10.77/10.99          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 10.77/10.99      inference('eq_fact', [status(thm)], ['0'])).
% 10.77/10.99  thf('2', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 10.77/10.99          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 10.77/10.99      inference('eq_fact', [status(thm)], ['0'])).
% 10.77/10.99  thf(t3_xboole_0, axiom,
% 10.77/10.99    (![A:$i,B:$i]:
% 10.77/10.99     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 10.77/10.99            ( r1_xboole_0 @ A @ B ) ) ) & 
% 10.77/10.99       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 10.77/10.99            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 10.77/10.99  thf('3', plain,
% 10.77/10.99      (![X6 : $i, X7 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 10.77/10.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 10.77/10.99  thf(d1_tarski, axiom,
% 10.77/10.99    (![A:$i,B:$i]:
% 10.77/10.99     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 10.77/10.99       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 10.77/10.99  thf('4', plain,
% 10.77/10.99      (![X12 : $i, X14 : $i, X15 : $i]:
% 10.77/10.99         (~ (r2_hidden @ X15 @ X14)
% 10.77/10.99          | ((X15) = (X12))
% 10.77/10.99          | ((X14) != (k1_tarski @ X12)))),
% 10.77/10.99      inference('cnf', [status(esa)], [d1_tarski])).
% 10.77/10.99  thf('5', plain,
% 10.77/10.99      (![X12 : $i, X15 : $i]:
% 10.77/10.99         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 10.77/10.99      inference('simplify', [status(thm)], ['4'])).
% 10.77/10.99  thf('6', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 10.77/10.99          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 10.77/10.99      inference('sup-', [status(thm)], ['3', '5'])).
% 10.77/10.99  thf('7', plain,
% 10.77/10.99      (![X6 : $i, X7 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 10.77/10.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 10.77/10.99  thf('8', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         ((r2_hidden @ X0 @ X1)
% 10.77/10.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 10.77/10.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 10.77/10.99      inference('sup+', [status(thm)], ['6', '7'])).
% 10.77/10.99  thf('9', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 10.77/10.99      inference('simplify', [status(thm)], ['8'])).
% 10.77/10.99  thf('10', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 10.77/10.99      inference('simplify', [status(thm)], ['8'])).
% 10.77/10.99  thf(t58_zfmisc_1, conjecture,
% 10.77/10.99    (![A:$i,B:$i]:
% 10.77/10.99     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 10.77/10.99       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 10.77/10.99  thf(zf_stmt_0, negated_conjecture,
% 10.77/10.99    (~( ![A:$i,B:$i]:
% 10.77/10.99        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 10.77/10.99          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 10.77/10.99    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 10.77/10.99  thf('11', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 10.77/10.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.77/10.99  thf('12', plain, ((r2_hidden @ sk_A @ sk_B)),
% 10.77/10.99      inference('sup-', [status(thm)], ['10', '11'])).
% 10.77/10.99  thf('13', plain,
% 10.77/10.99      (![X6 : $i, X7 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 10.77/10.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 10.77/10.99  thf('14', plain,
% 10.77/10.99      (![X12 : $i, X15 : $i]:
% 10.77/10.99         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 10.77/10.99      inference('simplify', [status(thm)], ['4'])).
% 10.77/10.99  thf('15', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 10.77/10.99          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 10.77/10.99      inference('sup-', [status(thm)], ['13', '14'])).
% 10.77/10.99  thf('16', plain,
% 10.77/10.99      (![X6 : $i, X7 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 10.77/10.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 10.77/10.99  thf('17', plain,
% 10.77/10.99      (![X6 : $i, X8 : $i, X9 : $i]:
% 10.77/10.99         (~ (r2_hidden @ X8 @ X6)
% 10.77/10.99          | ~ (r2_hidden @ X8 @ X9)
% 10.77/10.99          | ~ (r1_xboole_0 @ X6 @ X9))),
% 10.77/10.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 10.77/10.99  thf('18', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ X0 @ X1)
% 10.77/10.99          | ~ (r1_xboole_0 @ X0 @ X2)
% 10.77/10.99          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 10.77/10.99      inference('sup-', [status(thm)], ['16', '17'])).
% 10.77/10.99  thf('19', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.77/10.99         (~ (r2_hidden @ X0 @ X1)
% 10.77/10.99          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0))
% 10.77/10.99          | ~ (r1_xboole_0 @ X2 @ X1)
% 10.77/10.99          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0)))),
% 10.77/10.99      inference('sup-', [status(thm)], ['15', '18'])).
% 10.77/10.99  thf('20', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.77/10.99         (~ (r1_xboole_0 @ X2 @ X1)
% 10.77/10.99          | (r1_xboole_0 @ X2 @ (k1_tarski @ X0))
% 10.77/10.99          | ~ (r2_hidden @ X0 @ X1))),
% 10.77/10.99      inference('simplify', [status(thm)], ['19'])).
% 10.77/10.99  thf('21', plain,
% 10.77/10.99      (![X0 : $i]:
% 10.77/10.99         ((r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)) | ~ (r1_xboole_0 @ X0 @ sk_B))),
% 10.77/10.99      inference('sup-', [status(thm)], ['12', '20'])).
% 10.77/10.99  thf('22', plain,
% 10.77/10.99      (![X0 : $i]:
% 10.77/10.99         ((r2_hidden @ X0 @ sk_B)
% 10.77/10.99          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 10.77/10.99      inference('sup-', [status(thm)], ['9', '21'])).
% 10.77/10.99  thf('23', plain,
% 10.77/10.99      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.77/10.99         (((X13) != (X12))
% 10.77/10.99          | (r2_hidden @ X13 @ X14)
% 10.77/10.99          | ((X14) != (k1_tarski @ X12)))),
% 10.77/10.99      inference('cnf', [status(esa)], [d1_tarski])).
% 10.77/10.99  thf('24', plain, (![X12 : $i]: (r2_hidden @ X12 @ (k1_tarski @ X12))),
% 10.77/10.99      inference('simplify', [status(thm)], ['23'])).
% 10.77/10.99  thf('25', plain,
% 10.77/10.99      (![X6 : $i, X8 : $i, X9 : $i]:
% 10.77/10.99         (~ (r2_hidden @ X8 @ X6)
% 10.77/10.99          | ~ (r2_hidden @ X8 @ X9)
% 10.77/10.99          | ~ (r1_xboole_0 @ X6 @ X9))),
% 10.77/10.99      inference('cnf', [status(esa)], [t3_xboole_0])).
% 10.77/10.99  thf('26', plain,
% 10.77/10.99      (![X0 : $i, X1 : $i]:
% 10.77/10.99         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 10.77/10.99      inference('sup-', [status(thm)], ['24', '25'])).
% 10.77/10.99  thf('27', plain,
% 10.77/10.99      (![X0 : $i]:
% 10.77/10.99         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 10.77/10.99      inference('sup-', [status(thm)], ['22', '26'])).
% 10.77/10.99  thf('28', plain,
% 10.77/10.99      (![X0 : $i]:
% 10.77/10.99         (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 10.77/10.99          | (r2_hidden @ 
% 10.77/10.99             (sk_D @ (k1_tarski @ sk_A) @ X0 @ (k1_tarski @ sk_A)) @ sk_B))),
% 10.77/10.99      inference('sup-', [status(thm)], ['2', '27'])).
% 10.77/10.99  thf('29', plain,
% 10.77/10.99      (![X1 : $i, X2 : $i, X5 : $i]:
% 10.77/10.99         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 10.77/10.99          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 10.77/10.99          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 10.77/10.99          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 10.77/10.99      inference('cnf', [status(esa)], [d4_xboole_0])).
% 10.77/10.99  thf('30', plain,
% 10.77/10.99      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 10.77/10.99        | ~ (r2_hidden @ 
% 10.77/10.99             (sk_D @ (k1_tarski @ sk_A) @ sk_B @ (k1_tarski @ sk_A)) @ 
% 10.77/10.99             (k1_tarski @ sk_A))
% 10.77/10.99        | ~ (r2_hidden @ 
% 10.77/10.99             (sk_D @ (k1_tarski @ sk_A) @ sk_B @ (k1_tarski @ sk_A)) @ 
% 10.77/10.99             (k1_tarski @ sk_A))
% 10.77/10.99        | ((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 10.77/10.99      inference('sup-', [status(thm)], ['28', '29'])).
% 10.77/10.99  thf('31', plain,
% 10.77/10.99      ((~ (r2_hidden @ 
% 10.77/10.99           (sk_D @ (k1_tarski @ sk_A) @ sk_B @ (k1_tarski @ sk_A)) @ 
% 10.77/10.99           (k1_tarski @ sk_A))
% 10.77/10.99        | ((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 10.77/10.99      inference('simplify', [status(thm)], ['30'])).
% 10.77/10.99  thf('32', plain,
% 10.77/10.99      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 10.77/10.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.77/10.99  thf('33', plain,
% 10.77/10.99      (~ (r2_hidden @ 
% 10.77/10.99          (sk_D @ (k1_tarski @ sk_A) @ sk_B @ (k1_tarski @ sk_A)) @ 
% 10.77/10.99          (k1_tarski @ sk_A))),
% 10.77/10.99      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 10.77/10.99  thf('34', plain,
% 10.77/10.99      (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 10.77/10.99      inference('sup-', [status(thm)], ['1', '33'])).
% 10.77/10.99  thf('35', plain,
% 10.77/10.99      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 10.77/10.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.77/10.99  thf('36', plain, ($false),
% 10.77/10.99      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 10.77/10.99  
% 10.77/10.99  % SZS output end Refutation
% 10.77/10.99  
% 10.77/11.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
