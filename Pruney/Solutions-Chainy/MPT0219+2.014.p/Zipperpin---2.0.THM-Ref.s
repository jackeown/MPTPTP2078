%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0O2yOaWBA8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:05 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
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

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X19 @ X20 @ X17 ) ),
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
    ! [X29: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X32 @ X31 )
      | ( X32 = X29 )
      | ( X31
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X29: $i,X32: $i] :
      ( ( X32 = X29 )
      | ~ ( r2_hidden @ X32 @ ( k1_tarski @ X29 ) ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0O2yOaWBA8
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 361 iterations in 0.165s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(t13_zfmisc_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.62         ( k1_tarski @ A ) ) =>
% 0.38/0.62       ( ( A ) = ( B ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.62            ( k1_tarski @ A ) ) =>
% 0.38/0.62          ( ( A ) = ( B ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.38/0.62         = (k1_tarski @ sk_A))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.38/0.62         = (k1_tarski @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf(t41_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k2_tarski @ A @ B ) =
% 0.38/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X34 : $i, X35 : $i]:
% 0.38/0.62         ((k2_tarski @ X34 @ X35)
% 0.38/0.62           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.38/0.62  thf('4', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.62  thf(t70_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X44 : $i, X45 : $i]:
% 0.38/0.62         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 0.38/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.62  thf(d1_enumset1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.62       ( ![E:$i]:
% 0.38/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.62  thf(zf_stmt_2, axiom,
% 0.38/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_3, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.62       ( ![E:$i]:
% 0.38/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.62         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.38/0.62          | (r2_hidden @ X22 @ X26)
% 0.38/0.62          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.62         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 0.38/0.62          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 0.38/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['5', '7'])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.62         (((X18) != (X17)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.38/0.62         ~ (zip_tseitin_0 @ X17 @ X19 @ X20 @ X17)),
% 0.38/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['8', '10'])).
% 0.38/0.62  thf('12', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['4', '11'])).
% 0.38/0.62  thf(d1_tarski, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.38/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X32 @ X31)
% 0.38/0.62          | ((X32) = (X29))
% 0.38/0.62          | ((X31) != (k1_tarski @ X29)))),
% 0.38/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (![X29 : $i, X32 : $i]:
% 0.38/0.62         (((X32) = (X29)) | ~ (r2_hidden @ X32 @ (k1_tarski @ X29)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['13'])).
% 0.38/0.62  thf('15', plain, (((sk_B) = (sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['12', '14'])).
% 0.38/0.62  thf('16', plain, (((sk_A) != (sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('17', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
