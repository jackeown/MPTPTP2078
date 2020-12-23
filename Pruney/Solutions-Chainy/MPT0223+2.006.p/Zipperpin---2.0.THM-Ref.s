%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NUVyAf5ZA2

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:31 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   75 (  85 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  523 ( 621 expanded)
%              Number of equality atoms :   62 (  76 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['5','10','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
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

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X14 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NUVyAf5ZA2
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.65/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.83  % Solved by: fo/fo7.sh
% 0.65/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.83  % done 647 iterations in 0.382s
% 0.65/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.83  % SZS output start Refutation
% 0.65/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.65/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.65/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.83  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.65/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.83  thf(d1_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.65/0.83       ( ![E:$i]:
% 0.65/0.83         ( ( r2_hidden @ E @ D ) <=>
% 0.65/0.83           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.65/0.83  thf(zf_stmt_0, axiom,
% 0.65/0.83    (![E:$i,C:$i,B:$i,A:$i]:
% 0.65/0.83     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.65/0.83       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.65/0.83  thf('0', plain,
% 0.65/0.83      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.65/0.83         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.65/0.83          | ((X13) = (X14))
% 0.65/0.83          | ((X13) = (X15))
% 0.65/0.83          | ((X13) = (X16)))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf(t18_zfmisc_1, conjecture,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.65/0.83         ( k1_tarski @ A ) ) =>
% 0.65/0.83       ( ( A ) = ( B ) ) ))).
% 0.65/0.83  thf(zf_stmt_1, negated_conjecture,
% 0.65/0.83    (~( ![A:$i,B:$i]:
% 0.65/0.83        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.65/0.83            ( k1_tarski @ A ) ) =>
% 0.65/0.83          ( ( A ) = ( B ) ) ) )),
% 0.65/0.83    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.65/0.83  thf('1', plain,
% 0.65/0.83      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.65/0.83         = (k1_tarski @ sk_A))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.65/0.83  thf(t100_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.83  thf('2', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.65/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.83  thf('3', plain,
% 0.65/0.83      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.65/0.83         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.65/0.83      inference('sup+', [status(thm)], ['1', '2'])).
% 0.65/0.83  thf(t98_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.65/0.83  thf('4', plain,
% 0.65/0.83      (![X8 : $i, X9 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ X8 @ X9)
% 0.65/0.83           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.65/0.83  thf('5', plain,
% 0.65/0.83      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.65/0.83         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.65/0.83            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.65/0.83      inference('sup+', [status(thm)], ['3', '4'])).
% 0.65/0.83  thf(t21_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.65/0.83  thf('6', plain,
% 0.65/0.83      (![X2 : $i, X3 : $i]:
% 0.65/0.83         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.65/0.83      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.65/0.83  thf('7', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.65/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.83  thf('8', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.65/0.83           = (k5_xboole_0 @ X0 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['6', '7'])).
% 0.65/0.83  thf(t46_xboole_1, axiom,
% 0.65/0.83    (![A:$i,B:$i]:
% 0.65/0.83     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.65/0.83  thf('9', plain,
% 0.65/0.83      (![X6 : $i, X7 : $i]:
% 0.65/0.83         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 0.65/0.83      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.65/0.83  thf('10', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['8', '9'])).
% 0.65/0.83  thf(t2_boole, axiom,
% 0.65/0.83    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.65/0.83  thf('11', plain,
% 0.65/0.83      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.83      inference('cnf', [status(esa)], [t2_boole])).
% 0.65/0.83  thf('12', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.65/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.83  thf('13', plain,
% 0.65/0.83      (![X0 : $i]:
% 0.65/0.83         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['11', '12'])).
% 0.65/0.83  thf(t3_boole, axiom,
% 0.65/0.83    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.83  thf('14', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.65/0.83      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.83  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['13', '14'])).
% 0.65/0.83  thf('16', plain,
% 0.65/0.83      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.65/0.83         = (k1_tarski @ sk_B))),
% 0.65/0.83      inference('demod', [status(thm)], ['5', '10', '15'])).
% 0.65/0.83  thf(t69_enumset1, axiom,
% 0.65/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.65/0.83  thf('17', plain,
% 0.65/0.83      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.65/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.83  thf(t70_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.65/0.83  thf('18', plain,
% 0.65/0.83      (![X29 : $i, X30 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf(t46_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.65/0.83       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.65/0.83  thf('19', plain,
% 0.65/0.83      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X24 @ X25 @ X26 @ X27)
% 0.65/0.83           = (k2_xboole_0 @ (k1_enumset1 @ X24 @ X25 @ X26) @ (k1_tarski @ X27)))),
% 0.65/0.83      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.65/0.83  thf('20', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.65/0.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.65/0.83      inference('sup+', [status(thm)], ['18', '19'])).
% 0.65/0.83  thf(t71_enumset1, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i]:
% 0.65/0.83     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.65/0.83  thf('21', plain,
% 0.65/0.83      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.65/0.83           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.65/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.65/0.83  thf('22', plain,
% 0.65/0.83      (![X29 : $i, X30 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf('23', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['21', '22'])).
% 0.65/0.83  thf('24', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.65/0.83           = (k2_tarski @ X1 @ X0))),
% 0.65/0.83      inference('sup+', [status(thm)], ['20', '23'])).
% 0.65/0.83  thf('25', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.65/0.83           = (k2_tarski @ X0 @ X1))),
% 0.65/0.83      inference('sup+', [status(thm)], ['17', '24'])).
% 0.65/0.83  thf('26', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.65/0.83      inference('demod', [status(thm)], ['16', '25'])).
% 0.65/0.83  thf('27', plain,
% 0.65/0.83      (![X29 : $i, X30 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.65/0.83  thf(zf_stmt_3, axiom,
% 0.65/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.65/0.83       ( ![E:$i]:
% 0.65/0.83         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.65/0.83  thf('28', plain,
% 0.65/0.83      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.65/0.83         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.65/0.83          | (r2_hidden @ X17 @ X21)
% 0.65/0.83          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.65/0.83  thf('29', plain,
% 0.65/0.83      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.65/0.83         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.65/0.83          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.65/0.83      inference('simplify', [status(thm)], ['28'])).
% 0.65/0.83  thf('30', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.65/0.83          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.65/0.83      inference('sup+', [status(thm)], ['27', '29'])).
% 0.65/0.83  thf('31', plain,
% 0.65/0.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.65/0.83         (((X13) != (X14)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.83  thf('32', plain,
% 0.65/0.83      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.65/0.83         ~ (zip_tseitin_0 @ X14 @ X14 @ X15 @ X12)),
% 0.65/0.83      inference('simplify', [status(thm)], ['31'])).
% 0.65/0.83  thf('33', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.65/0.83      inference('sup-', [status(thm)], ['30', '32'])).
% 0.65/0.83  thf('34', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.65/0.83      inference('sup+', [status(thm)], ['26', '33'])).
% 0.65/0.83  thf('35', plain,
% 0.65/0.83      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.65/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.83  thf('36', plain,
% 0.65/0.83      (![X29 : $i, X30 : $i]:
% 0.65/0.83         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.65/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.83  thf('37', plain,
% 0.65/0.83      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.65/0.83         (~ (r2_hidden @ X22 @ X21)
% 0.65/0.83          | ~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.65/0.83          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.65/0.83  thf('38', plain,
% 0.65/0.83      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.65/0.83         (~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.65/0.83          | ~ (r2_hidden @ X22 @ (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.65/0.83      inference('simplify', [status(thm)], ['37'])).
% 0.65/0.83  thf('39', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.83         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.65/0.83          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.65/0.83      inference('sup-', [status(thm)], ['36', '38'])).
% 0.65/0.83  thf('40', plain,
% 0.65/0.83      (![X0 : $i, X1 : $i]:
% 0.65/0.83         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.65/0.83          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.65/0.83      inference('sup-', [status(thm)], ['35', '39'])).
% 0.65/0.83  thf('41', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.65/0.83      inference('sup-', [status(thm)], ['34', '40'])).
% 0.65/0.83  thf('42', plain,
% 0.65/0.83      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.65/0.83      inference('sup-', [status(thm)], ['0', '41'])).
% 0.65/0.83  thf('43', plain, (((sk_A) = (sk_B))),
% 0.65/0.83      inference('simplify', [status(thm)], ['42'])).
% 0.65/0.83  thf('44', plain, (((sk_A) != (sk_B))),
% 0.65/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.65/0.83  thf('45', plain, ($false),
% 0.65/0.83      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.65/0.83  
% 0.65/0.83  % SZS output end Refutation
% 0.65/0.83  
% 0.65/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
