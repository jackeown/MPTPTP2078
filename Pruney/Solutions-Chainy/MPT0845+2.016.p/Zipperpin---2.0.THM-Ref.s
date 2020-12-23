%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pq4R887vDg

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  383 ( 551 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( X18
        = ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X18 @ X14 @ X15 ) @ ( sk_E @ X18 @ X14 @ X15 ) @ ( sk_D @ X18 @ X14 @ X15 ) @ X14 @ X15 )
      | ( r2_hidden @ ( sk_D @ X18 @ X14 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('4',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_A )
      | ~ ( r1_xboole_0 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

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

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ( r2_hidden @ ( sk_C_1 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_A )
      | ~ ( r1_xboole_0 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( sk_C_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X26: $i] :
      ~ ( r2_hidden @ X26 @ sk_A ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_A @ X1 @ X0 ) @ X1 )
      | ( sk_A
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_F @ sk_A @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pq4R887vDg
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 91 iterations in 0.039s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.19/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.19/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.49  thf('0', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf(d2_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.49           ( ?[E:$i,F:$i]:
% 0.19/0.49             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.19/0.49               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.19/0.49  thf(zf_stmt_1, axiom,
% 0.19/0.49    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.19/0.49     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.19/0.49       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.19/0.49         ( r2_hidden @ E @ A ) ) ))).
% 0.19/0.49  thf(zf_stmt_2, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.49           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.19/0.49         (((X18) = (k2_zfmisc_1 @ X15 @ X14))
% 0.19/0.49          | (zip_tseitin_0 @ (sk_F @ X18 @ X14 @ X15) @ 
% 0.19/0.49             (sk_E @ X18 @ X14 @ X15) @ (sk_D @ X18 @ X14 @ X15) @ X14 @ X15)
% 0.19/0.49          | (r2_hidden @ (sk_D @ X18 @ X14 @ X15) @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         ((r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.19/0.49          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.19/0.49          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf(t1_mcart_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_3, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49             ( ![B:$i]:
% 0.19/0.49               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X26 : $i]: (~ (r2_hidden @ X26 @ sk_A) | ~ (r1_xboole_0 @ X26 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.49  thf(t3_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.49  thf(t7_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ~( ( r2_hidden @ A @ B ) & 
% 0.19/0.49          ( ![C:$i]:
% 0.19/0.49            ( ~( ( r2_hidden @ C @ B ) & 
% 0.19/0.49                 ( ![D:$i]:
% 0.19/0.49                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X21 @ X22) | (r2_hidden @ (sk_C_1 @ X22) @ X22))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X26 : $i]: (~ (r2_hidden @ X26 @ sk_A) | ~ (r1_xboole_0 @ X26 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X21 @ X22)
% 0.19/0.49          | ~ (r2_hidden @ X23 @ X22)
% 0.19/0.49          | ~ (r2_hidden @ X23 @ (sk_C_1 @ X22)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.49      inference('condensation', [status(thm)], ['12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.19/0.49          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.19/0.49          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '14'])).
% 0.19/0.49  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.49  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.19/0.49      inference('demod', [status(thm)], ['9', '16'])).
% 0.19/0.49  thf('18', plain, (![X26 : $i]: ~ (r2_hidden @ X26 @ sk_A)),
% 0.19/0.49      inference('demod', [status(thm)], ['4', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_F @ sk_A @ X1 @ X0) @ X1)
% 0.19/0.49          | ((sk_A) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '18'])).
% 0.19/0.49  thf(t7_ordinal1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((sk_A) = (k2_zfmisc_1 @ X1 @ X0))
% 0.19/0.49          | ~ (r1_tarski @ X0 @ (sk_F @ sk_A @ X0 @ X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain, (![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '21'])).
% 0.19/0.49  thf('23', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf('24', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.19/0.49          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.19/0.49          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.19/0.49          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.19/0.49          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ X2 @ X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1))
% 0.19/0.49          | (r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X24 : $i, X25 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0))
% 0.19/0.49          | ~ (r1_tarski @ X0 @ (sk_F @ k1_xboole_0 @ X0 @ X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['23', '30'])).
% 0.19/0.49  thf('32', plain, (((k1_xboole_0) = (sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['22', '31'])).
% 0.19/0.49  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.49  thf('34', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
