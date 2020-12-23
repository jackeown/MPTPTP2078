%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zFYj8b7HqT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:20 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  247 ( 295 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( X6 = X7 )
      | ( X6 = X8 )
      | ( X6 = X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[l20_zfmisc_1])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['5','7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
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

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zFYj8b7HqT
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:02:34 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 38 iterations in 0.022s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.50  thf(d1_enumset1, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.50       ( ![E:$i]:
% 0.24/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.24/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_0, axiom,
% 0.24/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.24/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.24/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.50         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.24/0.50          | ((X6) = (X7))
% 0.24/0.50          | ((X6) = (X8))
% 0.24/0.50          | ((X6) = (X9)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t25_zfmisc_1, conjecture,
% 0.24/0.50    (![A:$i,B:$i,C:$i]:
% 0.24/0.50     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.24/0.50          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.24/0.50  thf(zf_stmt_1, negated_conjecture,
% 0.24/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.50        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.24/0.50             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.50  thf(t12_xboole_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X3 : $i, X4 : $i]:
% 0.24/0.50         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.24/0.50         = (k2_tarski @ sk_B @ sk_C))),
% 0.24/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.50  thf(l20_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.24/0.50       ( r2_hidden @ A @ B ) ))).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X27 : $i, X28 : $i]:
% 0.24/0.50         ((r2_hidden @ X27 @ X28)
% 0.24/0.50          | ~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X27) @ X28) @ X28))),
% 0.24/0.50      inference('cnf', [status(esa)], [l20_zfmisc_1])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      ((~ (r1_tarski @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_B @ sk_C))
% 0.24/0.50        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.50  thf(d10_xboole_0, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.50  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.50  thf('8', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.24/0.50      inference('demod', [status(thm)], ['5', '7'])).
% 0.24/0.50  thf(t70_enumset1, axiom,
% 0.24/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (![X18 : $i, X19 : $i]:
% 0.24/0.50         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.24/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.24/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.24/0.50  thf(zf_stmt_3, axiom,
% 0.24/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.50       ( ![E:$i]:
% 0.24/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.24/0.50          | ~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.24/0.50          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.24/0.50         (~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.24/0.50          | ~ (r2_hidden @ X15 @ (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.24/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.24/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.24/0.50  thf('13', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.24/0.50      inference('sup-', [status(thm)], ['8', '12'])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '13'])).
% 0.24/0.50  thf('15', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.50  thf('16', plain, (((sk_A) != (sk_B))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.50  thf('17', plain, (((sk_A) != (sk_C))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.24/0.50  thf('18', plain, ($false),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['15', '16', '17'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
