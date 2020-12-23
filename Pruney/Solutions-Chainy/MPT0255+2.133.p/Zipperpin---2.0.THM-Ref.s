%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0tU5cOWeak

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  366 ( 411 expanded)
%              Number of equality atoms :   49 (  58 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k8_enumset1_type,type,(
    k8_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d8_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i,K: $i] :
      ( ( K
        = ( k8_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I @ J ) )
    <=> ! [L: $i] :
          ( ( r2_hidden @ L @ K )
        <=> ~ ( ( L != J )
              & ( L != I )
              & ( L != H )
              & ( L != G )
              & ( L != F )
              & ( L != E )
              & ( L != D )
              & ( L != C )
              & ( L != B )
              & ( L != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [L: $i,J: $i,I: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ L @ J @ I @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( L != A )
        & ( L != B )
        & ( L != C )
        & ( L != D )
        & ( L != E )
        & ( L != F )
        & ( L != G )
        & ( L != H )
        & ( L != I )
        & ( L != J ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i,J: $i,K: $i] :
      ( ( K
        = ( k8_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I @ J ) )
    <=> ! [L: $i] :
          ( ( r2_hidden @ L @ K )
        <=> ~ ( zip_tseitin_0 @ L @ J @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X16 @ X27 )
      | ( X27
       != ( k8_enumset1 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X16 @ ( k8_enumset1 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t15_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_xboole_1])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X30 @ X32 ) @ X31 )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['4'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X34 @ X35 ) )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X4: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X4 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0tU5cOWeak
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 29 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.21/0.49                                               $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(k8_enumset1_type, type, k8_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.49                                           $i > $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(d8_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i,K:$i]:
% 0.21/0.49     ( ( ( K ) = ( k8_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I @ J ) ) <=>
% 0.21/0.49       ( ![L:$i]:
% 0.21/0.49         ( ( r2_hidden @ L @ K ) <=>
% 0.21/0.49           ( ~( ( ( L ) != ( J ) ) & ( ( L ) != ( I ) ) & ( ( L ) != ( H ) ) & 
% 0.21/0.49                ( ( L ) != ( G ) ) & ( ( L ) != ( F ) ) & ( ( L ) != ( E ) ) & 
% 0.21/0.49                ( ( L ) != ( D ) ) & ( ( L ) != ( C ) ) & ( ( L ) != ( B ) ) & 
% 0.21/0.49                ( ( L ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, type, zip_tseitin_0 :
% 0.21/0.49      $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_1, axiom,
% 0.21/0.49    (![L:$i,J:$i,I:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ L @ J @ I @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.21/0.49       ( ( ( L ) != ( A ) ) & ( ( L ) != ( B ) ) & ( ( L ) != ( C ) ) & 
% 0.21/0.49         ( ( L ) != ( D ) ) & ( ( L ) != ( E ) ) & ( ( L ) != ( F ) ) & 
% 0.21/0.49         ( ( L ) != ( G ) ) & ( ( L ) != ( H ) ) & ( ( L ) != ( I ) ) & 
% 0.21/0.49         ( ( L ) != ( J ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i,J:$i,K:$i]:
% 0.21/0.49     ( ( ( K ) = ( k8_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I @ J ) ) <=>
% 0.21/0.49       ( ![L:$i]:
% 0.21/0.49         ( ( r2_hidden @ L @ K ) <=>
% 0.21/0.49           ( ~( zip_tseitin_0 @ L @ J @ I @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.49         X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.49         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ 
% 0.21/0.49           X24 @ X25 @ X26)
% 0.21/0.49          | (r2_hidden @ X16 @ X27)
% 0.21/0.49          | ((X27)
% 0.21/0.49              != (k8_enumset1 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 @ 
% 0.21/0.49                  X19 @ X18 @ X17)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.49         X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.49         ((r2_hidden @ X16 @ 
% 0.21/0.49           (k8_enumset1 @ X26 @ X25 @ X24 @ X23 @ X22 @ X21 @ X20 @ X19 @ 
% 0.21/0.49            X18 @ X17))
% 0.21/0.49          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ 
% 0.21/0.49             X24 @ X25 @ X26))),
% 0.21/0.49      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.49  thf(t50_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.21/0.49  thf(zf_stmt_3, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf(t15_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X0) = (k1_xboole_0)) | ((k2_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t15_xboole_1])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.49        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf(l38_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.21/0.49         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X30 @ X31)
% 0.21/0.49          | ((k4_xboole_0 @ (k2_tarski @ X30 @ X32) @ X31) != (k1_tarski @ X30)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_A))
% 0.21/0.49          | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t4_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_tarski @ sk_A)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.49  thf(t19_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.49       ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X34 : $i, X35 : $i]:
% 0.21/0.49         ((k3_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X34 @ X35))
% 0.21/0.49           = (k1_tarski @ X34))),
% 0.21/0.49      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf(t2_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.49  thf('14', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.21/0.49         X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ 
% 0.21/0.49          X9)),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 0.21/0.49         X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (((X5) != (X4))
% 0.21/0.49          | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ 
% 0.21/0.49               X13 @ X14 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X4 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.21/0.49         X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ 
% 0.21/0.49            X14 @ X4)),
% 0.21/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.49  thf('20', plain, ($false), inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
