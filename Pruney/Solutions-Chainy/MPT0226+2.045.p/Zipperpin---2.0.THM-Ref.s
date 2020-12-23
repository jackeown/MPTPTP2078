%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6GUlG0vIm

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:57 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   79 (  95 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  672 ( 841 expanded)
%              Number of equality atoms :   63 (  83 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('1',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('12',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k6_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('15',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k6_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k5_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('16',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('18',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X13 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W6GUlG0vIm
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 402 iterations in 0.119s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.57  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.40/0.57                                           $i > $i).
% 0.40/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.40/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.57  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(d1_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.57       ( ![E:$i]:
% 0.40/0.57         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.57           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, axiom,
% 0.40/0.57    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.57     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.57       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.57         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.40/0.57          | ((X12) = (X13))
% 0.40/0.57          | ((X12) = (X14))
% 0.40/0.57          | ((X12) = (X15)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(t21_zfmisc_1, conjecture,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.57         ( k1_xboole_0 ) ) =>
% 0.40/0.57       ( ( A ) = ( B ) ) ))).
% 0.40/0.57  thf(zf_stmt_1, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i]:
% 0.40/0.57        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.57            ( k1_xboole_0 ) ) =>
% 0.40/0.57          ( ( A ) = ( B ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.57  thf(t98_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.40/0.57  thf('2', plain,
% 0.40/0.57      (![X9 : $i, X10 : $i]:
% 0.40/0.57         ((k2_xboole_0 @ X9 @ X10)
% 0.40/0.57           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.57         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.40/0.57  thf(t5_boole, axiom,
% 0.40/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.57  thf('4', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.40/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.40/0.57         = (k1_tarski @ sk_B))),
% 0.40/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.40/0.57  thf(t69_enumset1, axiom,
% 0.40/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.57  thf('6', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.40/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.57  thf(t71_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.40/0.57         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 0.40/0.57           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 0.40/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.57  thf(t70_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X36 : $i, X37 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.40/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.57  thf(t72_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.40/0.57         ((k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44)
% 0.40/0.57           = (k2_enumset1 @ X41 @ X42 @ X43 @ X44))),
% 0.40/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.40/0.57  thf('11', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.57  thf(t74_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.57     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.40/0.57       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.40/0.57         ((k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.40/0.57           = (k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.40/0.57      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.40/0.57  thf(t68_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.40/0.57     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.40/0.57       ( k2_xboole_0 @
% 0.40/0.57         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 0.40/0.57         X34 : $i]:
% 0.40/0.57         ((k6_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.40/0.57           = (k2_xboole_0 @ 
% 0.40/0.57              (k5_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33) @ 
% 0.40/0.57              (k1_tarski @ X34)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.57         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.40/0.57           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.40/0.57              (k1_tarski @ X6)))),
% 0.40/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.40/0.57  thf(t75_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.40/0.57     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.40/0.57       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.40/0.57         ((k6_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62)
% 0.40/0.57           = (k5_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 0.40/0.57      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.40/0.57         ((k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.40/0.57           = (k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.40/0.57      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.57         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.57           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.57  thf(t73_enumset1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.57     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.40/0.57       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.40/0.57         ((k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.40/0.57           = (k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.40/0.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.57         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.57           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.57         ((k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.40/0.57           (k1_tarski @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['14', '19'])).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.40/0.57         ((k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.40/0.57           = (k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.40/0.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.57         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.40/0.57           (k1_tarski @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.40/0.57           = (k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2))),
% 0.40/0.57      inference('sup+', [status(thm)], ['11', '22'])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.40/0.57           = (k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1))),
% 0.40/0.57      inference('sup+', [status(thm)], ['6', '23'])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.40/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.40/0.57           = (k2_tarski @ X0 @ X1))),
% 0.40/0.57      inference('demod', [status(thm)], ['24', '25'])).
% 0.40/0.57  thf('27', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.40/0.57      inference('demod', [status(thm)], ['5', '26'])).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (![X36 : $i, X37 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.40/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.57  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.57  thf(zf_stmt_3, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.57       ( ![E:$i]:
% 0.40/0.57         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.57         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.40/0.57          | (r2_hidden @ X16 @ X20)
% 0.40/0.57          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.57  thf('30', plain,
% 0.40/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.57         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.40/0.57          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.40/0.57      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.57          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.57      inference('sup+', [status(thm)], ['28', '30'])).
% 0.40/0.57  thf('32', plain,
% 0.40/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (((X12) != (X13)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('33', plain,
% 0.40/0.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         ~ (zip_tseitin_0 @ X13 @ X13 @ X14 @ X11)),
% 0.40/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.40/0.57  thf('34', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['31', '33'])).
% 0.40/0.57  thf('35', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.40/0.57      inference('sup+', [status(thm)], ['27', '34'])).
% 0.40/0.57  thf('36', plain,
% 0.40/0.57      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.40/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.57  thf('37', plain,
% 0.40/0.57      (![X36 : $i, X37 : $i]:
% 0.40/0.57         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.40/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.57  thf('38', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X21 @ X20)
% 0.40/0.57          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.40/0.57          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.57  thf('39', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.40/0.57         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.40/0.57          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.57  thf('40', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.57          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['37', '39'])).
% 0.40/0.57  thf('41', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.40/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['36', '40'])).
% 0.40/0.57  thf('42', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.40/0.57      inference('sup-', [status(thm)], ['35', '41'])).
% 0.40/0.57  thf('43', plain,
% 0.40/0.57      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['0', '42'])).
% 0.40/0.57  thf('44', plain, (((sk_A) = (sk_B))),
% 0.40/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.40/0.57  thf('45', plain, (((sk_A) != (sk_B))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.57  thf('46', plain, ($false),
% 0.40/0.57      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
