%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W3CVkjPum2

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 353 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('5',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X2 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ~ ( zip_tseitin_0 @ X12 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W3CVkjPum2
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:24:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 38 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(d1_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.47       ( ![E:$i]:
% 0.20/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, axiom,
% 0.20/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.47          | ((X3) = (X4))
% 0.20/0.47          | ((X3) = (X5))
% 0.20/0.47          | ((X3) = (X6)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t25_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.47          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.47             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf(t12_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.47         = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf(t42_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.20/0.47           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_3, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.47       ( ![E:$i]:
% 0.20/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.47          | (r2_hidden @ X7 @ X11)
% 0.20/0.47          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.47         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.20/0.47          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.20/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.47          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['5', '7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (((X3) != (X2)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X2)),
% 0.20/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.47  thf('11', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.47  thf(t70_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X18 : $i, X19 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X12 @ X11)
% 0.20/0.47          | ~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.20/0.47          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.47         (~ (zip_tseitin_0 @ X12 @ X8 @ X9 @ X10)
% 0.20/0.47          | ~ (r2_hidden @ X12 @ (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.47          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.47  thf('16', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '16'])).
% 0.20/0.47  thf('18', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.47  thf('19', plain, (((sk_A) != (sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('20', plain, (((sk_A) != (sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.47  thf('21', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['18', '19', '20'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
