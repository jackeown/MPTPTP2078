%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UtO3Ly1Ui1

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  243 ( 291 expanded)
%              Number of equality atoms :   34 (  42 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('4',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ( X18 = X17 )
      | ( X18 = X14 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X18 = X14 )
      | ( X18 = X17 )
      | ~ ( r2_hidden @ X18 @ ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X2 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UtO3Ly1Ui1
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 44 iterations in 0.024s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.47  thf(t25_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.47          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.47             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t12_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.21/0.47         = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(t42_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(d1_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.47  thf(zf_stmt_2, axiom,
% 0.21/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_3, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.47       ( ![E:$i]:
% 0.21/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.47          | (r2_hidden @ X7 @ X11)
% 0.21/0.47          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.21/0.47          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.21/0.47          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['4', '6'])).
% 0.21/0.47  thf(d2_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.47       ( ![D:$i]:
% 0.21/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X14 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X18 @ X16)
% 0.21/0.47          | ((X18) = (X17))
% 0.21/0.47          | ((X18) = (X14))
% 0.21/0.47          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X14 : $i, X17 : $i, X18 : $i]:
% 0.21/0.47         (((X18) = (X14))
% 0.21/0.47          | ((X18) = (X17))
% 0.21/0.47          | ~ (r2_hidden @ X18 @ (k2_tarski @ X17 @ X14)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.47          | ((X0) = (sk_B))
% 0.21/0.47          | ((X0) = (sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         (((X3) != (X2)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X2)),
% 0.21/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.47  thf('13', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.47  thf('14', plain, (((sk_A) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, (((sk_A) != (sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['13', '14', '15'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
