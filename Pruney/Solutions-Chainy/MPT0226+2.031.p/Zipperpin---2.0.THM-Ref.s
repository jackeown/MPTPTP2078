%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nhkzHv1seb

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:55 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  401 ( 555 expanded)
%              Number of equality atoms :   52 (  74 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k2_tarski @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k2_tarski @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_B @ sk_A @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_B @ sk_A @ X0 )
      = ( k2_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ sk_B @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X14 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ sk_A @ X0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['1','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nhkzHv1seb
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 231 iterations in 0.121s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(t21_zfmisc_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.58         ( k1_xboole_0 ) ) =>
% 0.40/0.58       ( ( A ) = ( B ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.58            ( k1_xboole_0 ) ) =>
% 0.40/0.58          ( ( A ) = ( B ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.40/0.58  thf('0', plain, (((sk_A) != (sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d1_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.58       ( ![E:$i]:
% 0.40/0.58         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_1, axiom,
% 0.40/0.58    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.40/0.58          | ((X12) = (X13))
% 0.40/0.58          | ((X12) = (X14))
% 0.40/0.58          | ((X12) = (X15)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t98_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ X9 @ X10)
% 0.40/0.58           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.58  thf(commutativity_k5_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.40/0.58  thf(t5_boole, axiom,
% 0.40/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.58  thf('7', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.40/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.58  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.58         = (k1_tarski @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.40/0.58  thf(t69_enumset1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf(t43_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.40/0.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.58         ((k1_enumset1 @ X26 @ X27 @ X28)
% 0.40/0.58           = (k2_xboole_0 @ (k2_tarski @ X26 @ X27) @ (k1_tarski @ X28)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.58  thf(t70_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X30 : $i, X31 : $i]:
% 0.40/0.58         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.40/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k2_tarski @ X0 @ X1)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.40/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('15', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['9', '14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.58         ((k1_enumset1 @ X26 @ X27 @ X28)
% 0.40/0.58           = (k2_xboole_0 @ (k2_tarski @ X26 @ X27) @ (k1_tarski @ X28)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((k1_enumset1 @ sk_B @ sk_A @ X0)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k2_tarski @ X0 @ X1)
% 0.40/0.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.40/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i]: ((k1_enumset1 @ sk_B @ sk_A @ X0) = (k2_tarski @ sk_B @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.40/0.58  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_3, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.58       ( ![E:$i]:
% 0.40/0.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.40/0.58          | (r2_hidden @ X16 @ X20)
% 0.40/0.58          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.58         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.40/0.58          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.40/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((r2_hidden @ X1 @ (k2_tarski @ sk_B @ X0))
% 0.40/0.58          | (zip_tseitin_0 @ X1 @ X0 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['19', '21'])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.58         (((X12) != (X14)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.40/0.58         ~ (zip_tseitin_0 @ X14 @ X13 @ X14 @ X11)),
% 0.40/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.58  thf('25', plain, (![X0 : $i]: (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['22', '24'])).
% 0.40/0.58  thf('26', plain,
% 0.40/0.58      (![X30 : $i, X31 : $i]:
% 0.40/0.58         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.40/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X21 @ X20)
% 0.40/0.58          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.40/0.58          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.40/0.58         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.40/0.58          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.58         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.58          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '28'])).
% 0.40/0.58  thf('30', plain, (![X0 : $i]: ~ (zip_tseitin_0 @ sk_A @ X0 @ sk_B @ sk_B)),
% 0.40/0.58      inference('sup-', [status(thm)], ['25', '29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i]: (((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (X0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '30'])).
% 0.40/0.58  thf('32', plain, (![X0 : $i]: (((sk_A) = (X0)) | ((sk_A) = (sk_B)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.40/0.58  thf('33', plain, (((sk_A) != (sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('34', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('35', plain, (((sk_A) != (sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['0', '34'])).
% 0.40/0.58  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
