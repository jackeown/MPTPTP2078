%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JPu6YOcOE

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  268 ( 316 expanded)
%              Number of equality atoms :   37 (  45 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k2_tarski @ X22 @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

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

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X18 )
      | ( X20 = X19 )
      | ( X20 = X16 )
      | ( X18
       != ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('11',plain,(
    ! [X16: $i,X19: $i,X20: $i] :
      ( ( X20 = X16 )
      | ( X20 = X19 )
      | ~ ( r2_hidden @ X20 @ ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X6 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JPu6YOcOE
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:33:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 81 iterations in 0.043s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(t25_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.47          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.47             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t12_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.47         = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf(t43_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.47       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.47         ((k1_enumset1 @ X22 @ X23 @ X24)
% 0.20/0.47           = (k2_xboole_0 @ (k2_tarski @ X22 @ X23) @ (k1_tarski @ X24)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.20/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 0.20/0.47           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((k1_enumset1 @ sk_B @ sk_C @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.47  thf(d1_enumset1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.47       ( ![E:$i]:
% 0.20/0.47         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.47           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.47  thf(zf_stmt_2, axiom,
% 0.20/0.47    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.47     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.47       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_3, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.47       ( ![E:$i]:
% 0.20/0.47         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.47          | (r2_hidden @ X9 @ X13)
% 0.20/0.47          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.47         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.20/0.47          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.20/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.47          | (zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B))),
% 0.20/0.47      inference('sup+', [status(thm)], ['6', '8'])).
% 0.20/0.47  thf(d2_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.47       ( ![D:$i]:
% 0.20/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X20 @ X18)
% 0.20/0.47          | ((X20) = (X19))
% 0.20/0.47          | ((X20) = (X16))
% 0.20/0.47          | ((X18) != (k2_tarski @ X19 @ X16)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X16 : $i, X19 : $i, X20 : $i]:
% 0.20/0.47         (((X20) = (X16))
% 0.20/0.47          | ((X20) = (X19))
% 0.20/0.47          | ~ (r2_hidden @ X20 @ (k2_tarski @ X19 @ X16)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B)
% 0.20/0.47          | ((X0) = (sk_B))
% 0.20/0.47          | ((X0) = (sk_C)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         (((X5) != (X6)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X6 @ X6 @ X7 @ X4)),
% 0.20/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  thf('15', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.47  thf('16', plain, (((sk_A) != (sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, (((sk_A) != (sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['15', '16', '17'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
