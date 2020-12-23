%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x1sIIX6Cok

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:06 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   36 (  38 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  229 ( 251 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

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

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x1sIIX6Cok
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:50:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 285 iterations in 0.243s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.53/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.53/0.71  thf(t13_zfmisc_1, conjecture,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.53/0.71         ( k1_tarski @ A ) ) =>
% 0.53/0.71       ( ( A ) = ( B ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i]:
% 0.53/0.71        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.53/0.71            ( k1_tarski @ A ) ) =>
% 0.53/0.71          ( ( A ) = ( B ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.53/0.71         = (k1_tarski @ sk_A))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(commutativity_k2_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.53/0.71         = (k1_tarski @ sk_A))),
% 0.53/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.53/0.71  thf(t41_enumset1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( k2_tarski @ A @ B ) =
% 0.53/0.71       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      (![X30 : $i, X31 : $i]:
% 0.53/0.71         ((k2_tarski @ X30 @ X31)
% 0.53/0.71           = (k2_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X31)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.53/0.71  thf('4', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_A))),
% 0.53/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.71  thf(t70_enumset1, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      (![X40 : $i, X41 : $i]:
% 0.53/0.71         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.53/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.71  thf(d1_enumset1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.53/0.71       ( ![E:$i]:
% 0.53/0.71         ( ( r2_hidden @ E @ D ) <=>
% 0.53/0.71           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.53/0.71  thf(zf_stmt_2, axiom,
% 0.53/0.71    (![E:$i,C:$i,B:$i,A:$i]:
% 0.53/0.71     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.53/0.71       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_3, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.71     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.53/0.71       ( ![E:$i]:
% 0.53/0.71         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.53/0.71         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.53/0.71          | (r2_hidden @ X18 @ X22)
% 0.53/0.71          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.71         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.53/0.71          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.53/0.71      inference('simplify', [status(thm)], ['6'])).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.53/0.71          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.53/0.71      inference('sup+', [status(thm)], ['5', '7'])).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.71         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.53/0.71         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.53/0.71      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.71  thf('11', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '10'])).
% 0.53/0.71  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.53/0.71      inference('sup+', [status(thm)], ['4', '11'])).
% 0.53/0.71  thf(d1_tarski, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.53/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.53/0.71  thf('13', plain,
% 0.53/0.71      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X28 @ X27)
% 0.53/0.71          | ((X28) = (X25))
% 0.53/0.71          | ((X27) != (k1_tarski @ X25)))),
% 0.53/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      (![X25 : $i, X28 : $i]:
% 0.53/0.71         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['13'])).
% 0.53/0.71  thf('15', plain, (((sk_B) = (sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['12', '14'])).
% 0.53/0.71  thf('16', plain, (((sk_A) != (sk_B))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('17', plain, ($false),
% 0.53/0.71      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
