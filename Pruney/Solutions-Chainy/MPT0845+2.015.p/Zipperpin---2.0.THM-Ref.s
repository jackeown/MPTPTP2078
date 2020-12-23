%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ri4pEQBXtO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  317 ( 420 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_zfmisc_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( X17
        = ( k2_zfmisc_1 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X17 @ X13 @ X14 ) @ ( sk_E @ X17 @ X13 @ X14 ) @ ( sk_D @ X17 @ X13 @ X14 ) @ X13 @ X14 )
      | ( r2_hidden @ ( sk_D @ X17 @ X13 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ X7 )
      | ~ ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ~ ( r1_xboole_0 @ X28 @ sk_A ) ) ),
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

thf('6',plain,(
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

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ ( sk_C_1 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ sk_A )
      | ~ ( r1_xboole_0 @ X28 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( r2_hidden @ X27 @ ( sk_C_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X28: $i] :
      ~ ( r2_hidden @ X28 @ sk_A ) ),
    inference(demod,[status(thm)],['5','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_A @ X1 @ X0 ) @ X1 )
      | ( sk_A
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X21: $i] :
      ( ( k2_zfmisc_1 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ~ ( r2_hidden @ X23 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ri4pEQBXtO
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 79 iterations in 0.036s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(t113_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X21 : $i, X22 : $i]:
% 0.21/0.49         (((k2_zfmisc_1 @ X21 @ X22) = (k1_xboole_0))
% 0.21/0.49          | ((X22) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X21 : $i]: ((k2_zfmisc_1 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.49  thf(d2_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ?[E:$i,F:$i]:
% 0.21/0.49             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.49               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_1, axiom,
% 0.21/0.49    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.49       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.49         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.49  thf(zf_stmt_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.21/0.49         (((X17) = (k2_zfmisc_1 @ X14 @ X13))
% 0.21/0.49          | (zip_tseitin_0 @ (sk_F @ X17 @ X13 @ X14) @ 
% 0.21/0.49             (sk_E @ X17 @ X13 @ X14) @ (sk_D @ X17 @ X13 @ X14) @ X13 @ X14)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X17 @ X13 @ X14) @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         ((r2_hidden @ X5 @ X7) | ~ (zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.21/0.49          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.49          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t1_mcart_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49             ( ![B:$i]:
% 0.21/0.49               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ~ (r1_xboole_0 @ X28 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf(t3_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf(t7_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( r2_hidden @ A @ B ) & 
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.49                 ( ![D:$i]:
% 0.21/0.49                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X25 : $i, X26 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X25 @ X26) | (r2_hidden @ (sk_C_1 @ X26) @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X28 : $i]: (~ (r2_hidden @ X28 @ sk_A) | ~ (r1_xboole_0 @ X28 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X25 @ X26)
% 0.21/0.49          | ~ (r2_hidden @ X27 @ X26)
% 0.21/0.49          | ~ (r2_hidden @ X27 @ (sk_C_1 @ X26)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_tarski])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.49      inference('condensation', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.21/0.49          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.21/0.49          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '15'])).
% 0.21/0.49  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.49  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '17'])).
% 0.21/0.49  thf('19', plain, (![X28 : $i]: ~ (r2_hidden @ X28 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_F @ sk_A @ X1 @ X0) @ X1)
% 0.21/0.49          | ((sk_A) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X21 : $i]: ((k2_zfmisc_1 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.49  thf(t152_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X23 : $i, X24 : $i]: ~ (r2_hidden @ X23 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.49  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, (![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.49  thf('25', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '24'])).
% 0.21/0.49  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('27', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
