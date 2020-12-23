%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QHbxdubNYD

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:30 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  245 ( 263 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('7',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( X23 = X20 )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23 = X20 )
      | ~ ( r2_hidden @ X23 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QHbxdubNYD
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 266 iterations in 0.166s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.62  thf(t70_enumset1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X26 : $i, X27 : $i]:
% 0.40/0.62         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.40/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.62  thf(d1_enumset1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.62       ( ![E:$i]:
% 0.40/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.62  thf(zf_stmt_1, axiom,
% 0.40/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_2, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.62       ( ![E:$i]:
% 0.40/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.62         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.40/0.62          | (r2_hidden @ X13 @ X17)
% 0.40/0.62          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.62         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.40/0.62          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.40/0.62      inference('simplify', [status(thm)], ['1'])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['0', '2'])).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.40/0.62         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.40/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '5'])).
% 0.40/0.62  thf(t26_zfmisc_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.40/0.62       ( ( A ) = ( C ) ) ))).
% 0.40/0.62  thf(zf_stmt_3, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.62        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.40/0.62          ( ( A ) = ( C ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.62  thf(t28_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i]:
% 0.40/0.62         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.40/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))
% 0.40/0.62         = (k2_tarski @ sk_A @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.62  thf(d4_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.40/0.62       ( ![D:$i]:
% 0.40/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X4 @ X3)
% 0.40/0.62          | (r2_hidden @ X4 @ X2)
% 0.40/0.62          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.40/0.62         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.62          | (r2_hidden @ X0 @ (k1_tarski @ sk_C_1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['9', '11'])).
% 0.40/0.62  thf('13', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '12'])).
% 0.40/0.62  thf(d1_tarski, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X23 @ X22)
% 0.40/0.62          | ((X23) = (X20))
% 0.40/0.62          | ((X22) != (k1_tarski @ X20)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X20 : $i, X23 : $i]:
% 0.40/0.62         (((X23) = (X20)) | ~ (r2_hidden @ X23 @ (k1_tarski @ X20)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.62  thf('16', plain, (((sk_A) = (sk_C_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['13', '15'])).
% 0.40/0.62  thf('17', plain, (((sk_A) != (sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.62  thf('18', plain, ($false),
% 0.40/0.62      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
