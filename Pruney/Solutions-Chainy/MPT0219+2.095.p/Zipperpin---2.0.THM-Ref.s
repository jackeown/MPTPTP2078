%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQpC4fC2xR

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:16 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  252 ( 280 expanded)
%              Number of equality atoms :   34 (  39 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X5 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X5 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ( X18 = X17 )
      | ( X18 = X14 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('13',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X18 = X14 )
      | ( X18 = X17 )
      | ~ ( r2_hidden @ X18 @ ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UQpC4fC2xR
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 349 iterations in 0.147s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.59  thf(t13_zfmisc_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.59         ( k1_tarski @ A ) ) =>
% 0.37/0.59       ( ( A ) = ( B ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i]:
% 0.37/0.59        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.59            ( k1_tarski @ A ) ) =>
% 0.37/0.59          ( ( A ) = ( B ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.37/0.59         = (k1_tarski @ sk_A))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(t69_enumset1, axiom,
% 0.37/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.59  thf('1', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.37/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.59  thf(t42_enumset1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.37/0.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.59         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.37/0.59           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.37/0.59           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf(d1_enumset1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.59       ( ![E:$i]:
% 0.37/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_2, axiom,
% 0.37/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_3, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.59       ( ![E:$i]:
% 0.37/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.59         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.37/0.59          | (r2_hidden @ X7 @ X11)
% 0.37/0.59          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.59         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.37/0.59          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.37/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((r2_hidden @ X2 @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.37/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['3', '5'])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.37/0.59          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_A))),
% 0.37/0.59      inference('sup+', [status(thm)], ['0', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.59         (((X3) != (X5)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X5 @ X4 @ X5 @ X2)),
% 0.37/0.59      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.59  thf('10', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.37/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.59  thf(d2_tarski, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.37/0.59       ( ![D:$i]:
% 0.37/0.59         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X14 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X18 @ X16)
% 0.37/0.59          | ((X18) = (X17))
% 0.37/0.59          | ((X18) = (X14))
% 0.37/0.59          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d2_tarski])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (![X14 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         (((X18) = (X14))
% 0.37/0.59          | ((X18) = (X17))
% 0.37/0.59          | ~ (r2_hidden @ X18 @ (k2_tarski @ X17 @ X14)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['11', '13'])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.59  thf('16', plain, (((sk_B) = (sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['10', '15'])).
% 0.37/0.59  thf('17', plain, (((sk_A) != (sk_B))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('18', plain, ($false),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
