%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.03IyCKrZ7E

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  84 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  416 ( 747 expanded)
%              Number of equality atoms :   50 (  95 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X6 )
      | ( X3 = X4 )
      | ( X3 = X5 )
      | ( X3 = X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24
        = ( k1_zfmisc_1 @ X21 ) )
      | ( r1_tarski @ ( sk_C @ X24 @ X21 ) @ X21 )
      | ( r2_hidden @ ( sk_C @ X24 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_0 @ ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t1_zfmisc_1,conjecture,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf(zf_stmt_3,negated_conjecture,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t1_zfmisc_1])).

thf('15',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24
        = ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ ( sk_C @ X24 @ X21 ) @ X21 )
      | ~ ( r2_hidden @ ( sk_C @ X24 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,
    ( ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X2 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20','29'])).

thf('31',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.03IyCKrZ7E
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 50 iterations in 0.035s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(d1_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.50       ( ![E:$i]:
% 0.22/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, axiom,
% 0.22/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X3 @ X4 @ X5 @ X6)
% 0.22/0.50          | ((X3) = (X4))
% 0.22/0.50          | ((X3) = (X5))
% 0.22/0.50          | ((X3) = (X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d1_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X21 : $i, X24 : $i]:
% 0.22/0.50         (((X24) = (k1_zfmisc_1 @ X21))
% 0.22/0.50          | (r1_tarski @ (sk_C @ X24 @ X21) @ X21)
% 0.22/0.50          | (r2_hidden @ (sk_C @ X24 @ X21) @ X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.50  thf(t3_xboole_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.50          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.50          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf(t69_enumset1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.50  thf('4', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.50  thf(t70_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_2, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.50       ( ![E:$i]:
% 0.22/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X12 @ X11)
% 0.22/0.50          | ~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.22/0.50          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.22/0.50         (~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.22/0.50          | ~ (r2_hidden @ X12 @ (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.50          | ~ (zip_tseitin_0 @ (sk_C @ (k1_tarski @ X0) @ k1_xboole_0) @ X0 @ 
% 0.22/0.50               X0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (X0))
% 0.22/0.50          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (X0))
% 0.22/0.50          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (X0))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.50          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.50          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) != (k1_xboole_0))
% 0.22/0.50          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.50          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.50      inference('eq_fact', [status(thm)], ['12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf(t1_zfmisc_1, conjecture,
% 0.22/0.50    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.22/0.50  thf(zf_stmt_3, negated_conjecture,
% 0.22/0.50    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X21 : $i, X24 : $i]:
% 0.22/0.50         (((X24) = (k1_zfmisc_1 @ X21))
% 0.22/0.50          | ~ (r1_tarski @ (sk_C @ X24 @ X21) @ X21)
% 0.22/0.50          | ~ (r2_hidden @ (sk_C @ X24 @ X21) @ X24))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.50        | ~ (r2_hidden @ (sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.22/0.50             (k1_tarski @ k1_xboole_0))
% 0.22/0.50        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.22/0.50          | (r2_hidden @ X7 @ X11)
% 0.22/0.50          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.22/0.50          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.22/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['22', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.50         (((X3) != (X2)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X2)),
% 0.22/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '27'])).
% 0.22/0.50  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['21', '28'])).
% 0.22/0.50  thf('30', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19', '20', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('32', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
