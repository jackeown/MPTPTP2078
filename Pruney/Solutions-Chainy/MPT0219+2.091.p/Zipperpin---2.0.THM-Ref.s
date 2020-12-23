%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uF46IvuYxm

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  212 ( 234 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

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
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uF46IvuYxm
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 22 iterations in 0.015s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(t13_zfmisc_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46         ( k1_tarski @ A ) ) =>
% 0.20/0.46       ( ( A ) = ( B ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.46            ( k1_tarski @ A ) ) =>
% 0.20/0.46          ( ( A ) = ( B ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.46         = (k1_tarski @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t69_enumset1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.46  thf('1', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.20/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.46  thf(t42_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.46       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.46         ((k1_enumset1 @ X19 @ X20 @ X21)
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k2_tarski @ X20 @ X21)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.20/0.46           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, (((k1_enumset1 @ sk_A @ sk_B @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.46  thf(d1_enumset1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.46       ( ![E:$i]:
% 0.20/0.46         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.46           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.46  thf(zf_stmt_2, axiom,
% 0.20/0.46    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.46     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.46       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_3, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.46       ( ![E:$i]:
% 0.20/0.46         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.46         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.20/0.46          | (r2_hidden @ X7 @ X11)
% 0.20/0.46          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.46         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.20/0.46          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.20/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.46          | (zip_tseitin_0 @ X0 @ sk_B @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (((X3) != (X5)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X5 @ X4 @ X5 @ X2)),
% 0.20/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.46  thf('10', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.46  thf(d1_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X17 @ X16)
% 0.20/0.46          | ((X17) = (X14))
% 0.20/0.46          | ((X16) != (k1_tarski @ X14)))),
% 0.20/0.46      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X14 : $i, X17 : $i]:
% 0.20/0.46         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.46  thf('13', plain, (((sk_B) = (sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.46  thf('14', plain, (((sk_A) != (sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
