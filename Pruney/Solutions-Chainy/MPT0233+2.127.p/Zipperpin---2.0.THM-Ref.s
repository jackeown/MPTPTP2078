%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.44RbjumzUn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  64 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  378 ( 488 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(clc,[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_D_1 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','28'])).

thf('30',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.44RbjumzUn
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:48:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 77 iterations in 0.072s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(d1_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.52       ( ![E:$i]:
% 0.20/0.52         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, axiom,
% 0.20/0.52    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.52          | ((X13) = (X14))
% 0.20/0.52          | ((X13) = (X15))
% 0.20/0.52          | ((X13) = (X16)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t28_zfmisc_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.52          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.52             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.52  thf(l32_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X9 : $i, X11 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.20/0.52         = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t70_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X24 : $i, X25 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.52  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_3, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.52       ( ![E:$i]:
% 0.20/0.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.20/0.52          | (r2_hidden @ X17 @ X21)
% 0.20/0.52          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.52         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.20/0.52          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.20/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.52          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.52         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.20/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.52  thf(d5_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | (r2_hidden @ X0 @ X3)
% 0.20/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((r2_hidden @ X1 @ X2)
% 0.20/0.52          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.20/0.52        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '13'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('16', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.20/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X9 : $i, X11 : $i]:
% 0.20/0.52         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.52  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.52          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.52  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('condensation', [status(thm)], ['21'])).
% 0.20/0.52  thf('23', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X24 : $i, X25 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.20/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X22 @ X21)
% 0.20/0.52          | ~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.20/0.52          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.20/0.52         (~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.20/0.52          | ~ (r2_hidden @ X22 @ (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.52          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.52  thf('28', plain, (~ (zip_tseitin_0 @ sk_A @ sk_D_1 @ sk_C @ sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      ((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_D_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '28'])).
% 0.20/0.52  thf('30', plain, ((((sk_A) = (sk_D_1)) | ((sk_A) = (sk_C)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.52  thf('31', plain, (((sk_A) != (sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.52  thf('32', plain, (((sk_A) != (sk_D_1))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.52  thf('33', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['30', '31', '32'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
