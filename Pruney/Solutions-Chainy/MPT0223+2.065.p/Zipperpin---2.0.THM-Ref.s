%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jfg4UDqFOD

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (  86 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  527 ( 625 expanded)
%              Number of equality atoms :   63 (  77 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( X11 = X12 )
      | ( X11 = X13 )
      | ( X11 = X14 ) ) ),
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

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','8'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X25 @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X32 @ X32 @ X33 @ X34 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
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

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X12 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','42'])).

thf('44',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jfg4UDqFOD
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 21:03:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 430 iterations in 0.132s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.59  thf(d1_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.59       ( ![E:$i]:
% 0.21/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, axiom,
% 0.21/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.59         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.59          | ((X11) = (X12))
% 0.21/0.59          | ((X11) = (X13))
% 0.21/0.59          | ((X11) = (X14)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf(t18_zfmisc_1, conjecture,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.59         ( k1_tarski @ A ) ) =>
% 0.21/0.59       ( ( A ) = ( B ) ) ))).
% 0.21/0.59  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.59    (~( ![A:$i,B:$i]:
% 0.21/0.59        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.59            ( k1_tarski @ A ) ) =>
% 0.21/0.59          ( ( A ) = ( B ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.59         = (k1_tarski @ sk_A))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.59  thf(t100_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.59  thf(t21_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (![X2 : $i, X3 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.21/0.59      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.21/0.59           = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.59  thf(t46_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X6 : $i, X7 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 0.21/0.59      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.59  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.21/0.59      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.59  thf(t98_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X8 : $i, X9 : $i]:
% 0.21/0.59         ((k2_xboole_0 @ X8 @ X9)
% 0.21/0.59           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.59         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.59  thf(t2_boole, axiom,
% 0.21/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.59  thf('14', plain,
% 0.21/0.59      (![X0 : $i]:
% 0.21/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.59  thf(t3_boole, axiom,
% 0.21/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.59  thf('15', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.59  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.59         = (k1_tarski @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.59  thf(t69_enumset1, axiom,
% 0.21/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf(t70_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      (![X30 : $i, X31 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.21/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.59  thf(t46_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.59     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.59       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X25 @ X26 @ X27 @ X28)
% 0.21/0.59           = (k2_xboole_0 @ (k1_enumset1 @ X25 @ X26 @ X27) @ (k1_tarski @ X28)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.21/0.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.59  thf('22', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['18', '21'])).
% 0.21/0.59  thf(t71_enumset1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X32 @ X32 @ X33 @ X34)
% 0.21/0.59           = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.21/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      (![X30 : $i, X31 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.21/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.59      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         ((k2_tarski @ X0 @ X1)
% 0.21/0.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.59      inference('demod', [status(thm)], ['22', '25'])).
% 0.21/0.59  thf('27', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.21/0.59      inference('demod', [status(thm)], ['17', '26'])).
% 0.21/0.59  thf('28', plain,
% 0.21/0.59      (![X30 : $i, X31 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.21/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.59  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.59  thf(zf_stmt_3, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.59       ( ![E:$i]:
% 0.21/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.59  thf('29', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.59         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.21/0.59          | (r2_hidden @ X15 @ X19)
% 0.21/0.59          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.59  thf('30', plain,
% 0.21/0.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.59         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.21/0.59          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.21/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.59  thf('31', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.59      inference('sup+', [status(thm)], ['28', '30'])).
% 0.21/0.59  thf('32', plain,
% 0.21/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.59         (((X11) != (X12)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('33', plain,
% 0.21/0.59      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.59         ~ (zip_tseitin_0 @ X12 @ X12 @ X13 @ X10)),
% 0.21/0.59      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.59  thf('34', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.59  thf('35', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.59      inference('sup+', [status(thm)], ['27', '34'])).
% 0.21/0.59  thf('36', plain,
% 0.21/0.59      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.21/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.59  thf('37', plain,
% 0.21/0.59      (![X30 : $i, X31 : $i]:
% 0.21/0.59         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 0.21/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.59  thf('38', plain,
% 0.21/0.59      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X20 @ X19)
% 0.21/0.59          | ~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.21/0.59          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.59  thf('39', plain,
% 0.21/0.59      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.21/0.59         (~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.21/0.59          | ~ (r2_hidden @ X20 @ (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.21/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.59  thf('40', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['37', '39'])).
% 0.21/0.59  thf('41', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['36', '40'])).
% 0.21/0.59  thf('42', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.21/0.59      inference('sup-', [status(thm)], ['35', '41'])).
% 0.21/0.59  thf('43', plain,
% 0.21/0.59      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['0', '42'])).
% 0.21/0.59  thf('44', plain, (((sk_A) = (sk_B))),
% 0.21/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.59  thf('45', plain, (((sk_A) != (sk_B))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.59  thf('46', plain, ($false),
% 0.21/0.59      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
