%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GP8A3TaHC6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:43 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  200 ( 200 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t19_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t19_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X82: $i,X83: $i] :
      ( ( k1_enumset1 @ X82 @ X82 @ X83 )
      = ( k2_tarski @ X82 @ X83 ) ) ),
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

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('8',plain,(
    ! [X109: $i,X110: $i] :
      ( ( ( k3_xboole_0 @ X110 @ ( k1_tarski @ X109 ) )
        = ( k1_tarski @ X109 ) )
      | ~ ( r2_hidden @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GP8A3TaHC6
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:17:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 478 iterations in 0.303s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.76  thf(t19_zfmisc_1, conjecture,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.58/0.76       ( k1_tarski @ A ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i,B:$i]:
% 0.58/0.76        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.58/0.76          ( k1_tarski @ A ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t19_zfmisc_1])).
% 0.58/0.76  thf('0', plain,
% 0.58/0.76      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.58/0.76         != (k1_tarski @ sk_A))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t70_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      (![X82 : $i, X83 : $i]:
% 0.58/0.76         ((k1_enumset1 @ X82 @ X82 @ X83) = (k2_tarski @ X82 @ X83))),
% 0.58/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.76  thf(d1_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.76       ( ![E:$i]:
% 0.58/0.76         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.76           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.76  thf(zf_stmt_2, axiom,
% 0.58/0.76    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.76     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.76       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_3, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.76       ( ![E:$i]:
% 0.58/0.76         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.76         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.58/0.76          | (r2_hidden @ X19 @ X23)
% 0.58/0.76          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.76         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.58/0.76          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.58/0.76      inference('simplify', [status(thm)], ['2'])).
% 0.58/0.76  thf('4', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.76          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['1', '3'])).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.76         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.76  thf('6', plain,
% 0.58/0.76      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.58/0.76         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.58/0.76      inference('simplify', [status(thm)], ['5'])).
% 0.58/0.76  thf('7', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['4', '6'])).
% 0.58/0.76  thf(l31_zfmisc_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r2_hidden @ A @ B ) =>
% 0.58/0.76       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X109 : $i, X110 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X110 @ (k1_tarski @ X109)) = (k1_tarski @ X109))
% 0.58/0.76          | ~ (r2_hidden @ X109 @ X110))),
% 0.58/0.76      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.58/0.76           = (k1_tarski @ X1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.76  thf('11', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.58/0.76           = (k1_tarski @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['9', '10'])).
% 0.58/0.76  thf('12', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '11'])).
% 0.58/0.76  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.58/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
