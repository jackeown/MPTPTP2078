%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EnrdaPpZi8

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (  77 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  452 ( 538 expanded)
%              Number of equality atoms :   56 (  69 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('7',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['7','19','20'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X13 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EnrdaPpZi8
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 135 iterations in 0.052s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(d1_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.50       ( ![E:$i]:
% 0.20/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, axiom,
% 0.20/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.20/0.50          | ((X12) = (X13))
% 0.20/0.50          | ((X12) = (X14))
% 0.20/0.50          | ((X12) = (X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t18_zfmisc_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.50         ( k1_tarski @ A ) ) =>
% 0.20/0.50       ( ( A ) = ( B ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.50            ( k1_tarski @ A ) ) =>
% 0.20/0.50          ( ( A ) = ( B ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.50         = (k1_tarski @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf(t100_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.50         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(t98_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ X7 @ X8)
% 0.20/0.50           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.20/0.50         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.20/0.50            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf(t41_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_tarski @ A @ B ) =
% 0.20/0.50       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i]:
% 0.20/0.50         ((k2_tarski @ X23 @ X24)
% 0.20/0.50           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((k2_tarski @ sk_B @ sk_A)
% 0.20/0.50         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.20/0.50            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf(t2_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t5_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('11', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.50  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf(t48_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.20/0.50           = (k3_xboole_0 @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         ((k4_xboole_0 @ X1 @ X2)
% 0.20/0.50           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.50  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.20/0.50  thf('20', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.50  thf('21', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '19', '20'])).
% 0.20/0.50  thf(t70_enumset1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X26 : $i, X27 : $i]:
% 0.20/0.50         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.50       ( ![E:$i]:
% 0.20/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.50          | (r2_hidden @ X16 @ X20)
% 0.20/0.50          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.50         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.20/0.50          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.20/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['22', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         (((X12) != (X13)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ~ (zip_tseitin_0 @ X13 @ X13 @ X14 @ X11)),
% 0.20/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '27'])).
% 0.20/0.50  thf('29', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['21', '28'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X26 : $i, X27 : $i]:
% 0.20/0.50         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X21 @ X20)
% 0.20/0.50          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.20/0.50          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.20/0.50         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.20/0.50          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '34'])).
% 0.20/0.50  thf('36', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '36'])).
% 0.20/0.50  thf('38', plain, (((sk_A) = (sk_B))),
% 0.20/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.50  thf('39', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.50  thf('40', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
