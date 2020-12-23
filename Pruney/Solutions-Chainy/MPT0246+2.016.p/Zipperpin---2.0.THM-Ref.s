%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i9QSDwRh9o

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  93 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  506 (1046 expanded)
%              Number of equality atoms :   75 ( 170 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X5 )
      | ( X2 = X3 )
      | ( X2 = X4 )
      | ( X2 = X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k1_enumset1 @ X9 @ X8 @ X7 ) )
      | ~ ( zip_tseitin_0 @ ( sk_E @ X12 @ X7 @ X8 @ X9 ) @ X7 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_E @ X12 @ X7 @ X8 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_E @ X3 @ X2 @ X1 @ X0 )
        = X0 )
      | ( ( sk_E @ X3 @ X2 @ X1 @ X0 )
        = X1 )
      | ( ( sk_E @ X3 @ X2 @ X1 @ X0 )
        = X2 )
      | ( r2_hidden @ ( sk_E @ X3 @ X2 @ X1 @ X0 ) @ X3 )
      | ( X3
        = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('3',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ( X41 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_enumset1 @ X0 @ X1 @ X2 ) )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = X2 )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = X1 )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = X0 )
      | ( ( sk_E @ sk_A @ X2 @ X1 @ X0 )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != sk_B_1 )
      | ( ( sk_E @ sk_A @ X0 @ X2 @ X1 )
        = sk_B_1 )
      | ( ( sk_E @ sk_A @ X0 @ X2 @ X1 )
        = X1 )
      | ( ( sk_E @ sk_A @ X0 @ X2 @ X1 )
        = X2 )
      | ( sk_A
        = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( sk_A
        = ( k1_enumset1 @ X1 @ X2 @ sk_B_1 ) )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X2 @ X1 )
        = X2 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X2 @ X1 )
        = X1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X2 @ X1 )
        = sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_B_1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X0 @ X1 )
        = sk_B_1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ X0 @ X1 )
        = X1 )
      | ( sk_A
        = ( k1_enumset1 @ X1 @ X0 @ sk_B_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( sk_A
        = ( k1_enumset1 @ X1 @ sk_B_1 @ sk_B_1 ) )
      | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1 )
        = X1 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1 )
        = sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X0 )
        = X0 )
      | ( sk_A
        = ( k1_enumset1 @ X0 @ sk_B_1 @ sk_B_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A
      = ( k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) )
    | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k1_enumset1 @ X9 @ X8 @ X7 ) )
      | ( zip_tseitin_0 @ ( sk_E @ X12 @ X7 @ X8 @ X9 ) @ X7 @ X8 @ X9 )
      | ~ ( r2_hidden @ ( sk_E @ X12 @ X7 @ X8 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 ) @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    | ( sk_A
      = ( k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ sk_A )
      | ( X41 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('24',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,
    ( ( zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','26','27','28','29'])).

thf('31',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X4 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ~ ( zip_tseitin_0 @ X1 @ X3 @ X4 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['32','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i9QSDwRh9o
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:16:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 118 iterations in 0.054s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(d1_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.52       ( ![E:$i]:
% 0.21/0.52         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, axiom,
% 0.21/0.52    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X2 @ X3 @ X4 @ X5)
% 0.21/0.52          | ((X2) = (X3))
% 0.21/0.52          | ((X2) = (X4))
% 0.21/0.52          | ((X2) = (X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.52       ( ![E:$i]:
% 0.21/0.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X12 : $i]:
% 0.21/0.52         (((X12) = (k1_enumset1 @ X9 @ X8 @ X7))
% 0.21/0.52          | ~ (zip_tseitin_0 @ (sk_E @ X12 @ X7 @ X8 @ X9) @ X7 @ X8 @ X9)
% 0.21/0.52          | (r2_hidden @ (sk_E @ X12 @ X7 @ X8 @ X9) @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (((sk_E @ X3 @ X2 @ X1 @ X0) = (X0))
% 0.21/0.52          | ((sk_E @ X3 @ X2 @ X1 @ X0) = (X1))
% 0.21/0.52          | ((sk_E @ X3 @ X2 @ X1 @ X0) = (X2))
% 0.21/0.52          | (r2_hidden @ (sk_E @ X3 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.52          | ((X3) = (k1_enumset1 @ X0 @ X1 @ X2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf(t41_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X41 : $i]: (~ (r2_hidden @ X41 @ sk_A) | ((X41) = (sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((sk_A) = (k1_enumset1 @ X0 @ X1 @ X2))
% 0.21/0.52          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (X2))
% 0.21/0.52          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (X1))
% 0.21/0.52          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (X0))
% 0.21/0.52          | ((sk_E @ sk_A @ X2 @ X1 @ X0) = (sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((X0) != (sk_B_1))
% 0.21/0.52          | ((sk_E @ sk_A @ X0 @ X2 @ X1) = (sk_B_1))
% 0.21/0.52          | ((sk_E @ sk_A @ X0 @ X2 @ X1) = (X1))
% 0.21/0.52          | ((sk_E @ sk_A @ X0 @ X2 @ X1) = (X2))
% 0.21/0.52          | ((sk_A) = (k1_enumset1 @ X1 @ X2 @ X0)))),
% 0.21/0.52      inference('eq_fact', [status(thm)], ['4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         (((sk_A) = (k1_enumset1 @ X1 @ X2 @ sk_B_1))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ X2 @ X1) = (X2))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ X2 @ X1) = (X1))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ X2 @ X1) = (sk_B_1)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X0) != (sk_B_1))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ X0 @ X1) = (sk_B_1))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ X0 @ X1) = (X1))
% 0.21/0.52          | ((sk_A) = (k1_enumset1 @ X1 @ X0 @ sk_B_1)))),
% 0.21/0.52      inference('eq_fact', [status(thm)], ['6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X1 : $i]:
% 0.21/0.52         (((sk_A) = (k1_enumset1 @ X1 @ sk_B_1 @ sk_B_1))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1) = (X1))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X1) = (sk_B_1)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_B_1) != (X0))
% 0.21/0.52          | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ X0) = (X0))
% 0.21/0.52          | ((sk_A) = (k1_enumset1 @ X0 @ sk_B_1 @ sk_B_1)))),
% 0.21/0.52      inference('eq_fact', [status(thm)], ['8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((((sk_A) = (k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1))
% 0.21/0.52        | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.52  thf(t70_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf(t69_enumset1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((((sk_A) = (k1_tarski @ sk_B_1))
% 0.21/0.52        | ((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.52  thf('14', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('15', plain, (((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X12 : $i]:
% 0.21/0.52         (((X12) = (k1_enumset1 @ X9 @ X8 @ X7))
% 0.21/0.52          | (zip_tseitin_0 @ (sk_E @ X12 @ X7 @ X8 @ X9) @ X7 @ X8 @ X9)
% 0.21/0.52          | ~ (r2_hidden @ (sk_E @ X12 @ X7 @ X8 @ X9) @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.21/0.52        | (zip_tseitin_0 @ (sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) @ sk_B_1 @ 
% 0.21/0.52           sk_B_1 @ sk_B_1)
% 0.21/0.52        | ((sk_A) = (k1_enumset1 @ sk_B_1 @ sk_B_1 @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf(t7_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X41 : $i]: (~ (r2_hidden @ X41 @ sk_A) | ((X41) = (sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('20', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('22', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('24', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('26', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain, (((sk_E @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1) = (sk_B_1))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1)
% 0.21/0.52        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '26', '27', '28', '29'])).
% 0.21/0.52  thf('31', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('32', plain, ((zip_tseitin_0 @ sk_B_1 @ sk_B_1 @ sk_B_1 @ sk_B_1)),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (((X2) != (X1)) | ~ (zip_tseitin_0 @ X2 @ X3 @ X4 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X1 : $i, X3 : $i, X4 : $i]: ~ (zip_tseitin_0 @ X1 @ X3 @ X4 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.52  thf('35', plain, ($false), inference('sup-', [status(thm)], ['32', '34'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
