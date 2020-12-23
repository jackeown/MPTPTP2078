%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bFeNzYu2nv

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:24 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 103 expanded)
%              Number of leaves         :   36 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  702 ( 967 expanded)
%              Number of equality atoms :   67 (  92 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t81_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('15',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k6_enumset1 @ X50 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('16',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('17',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('18',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('30',plain,
    ( ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['11','28','29'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bFeNzYu2nv
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 215 iterations in 0.184s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.38/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.61  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.61  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.61  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.38/0.61                                           $i > $i).
% 0.38/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(d1_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.61       ( ![E:$i]:
% 0.38/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, axiom,
% 0.38/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.61         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.38/0.61          | ((X9) = (X10))
% 0.38/0.61          | ((X9) = (X11))
% 0.38/0.61          | ((X9) = (X12)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t25_zfmisc_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.38/0.61          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.61        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.38/0.61             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.61  thf(t28_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]:
% 0.38/0.61         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.38/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.38/0.61         = (k1_tarski @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf(t100_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.38/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.61  thf(t92_xboole_1, axiom,
% 0.38/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.61  thf('6', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.38/0.61         = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['5', '6'])).
% 0.38/0.61  thf(t98_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X6 : $i, X7 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X6 @ X7)
% 0.38/0.61           = (k5_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.38/0.61         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.61  thf(t5_boole, axiom,
% 0.38/0.61    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.61  thf('10', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.38/0.61         = (k2_tarski @ sk_B @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.61  thf(t71_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.38/0.61           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.61  thf(t70_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X29 : $i, X30 : $i]:
% 0.38/0.61         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.38/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.61  thf(t81_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.61     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.38/0.61       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.38/0.61         ((k6_enumset1 @ X50 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.38/0.61           = (k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.38/0.61      inference('cnf', [status(esa)], [t81_enumset1])).
% 0.38/0.61  thf(t75_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.38/0.61     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.38/0.61       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.38/0.61         ((k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.38/0.61           = (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.38/0.61      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.38/0.61         ((k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.38/0.61           = (k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.38/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.61  thf(t73_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.38/0.61     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.38/0.61       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.38/0.61         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.38/0.61           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.38/0.61      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.61         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.61           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf(t72_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.38/0.61         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 0.38/0.61           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 0.38/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.61           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.61  thf(t68_enumset1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.38/0.61     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.38/0.61       ( k2_xboole_0 @
% 0.38/0.61         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, 
% 0.38/0.61         X27 : $i]:
% 0.38/0.61         ((k6_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.38/0.61           = (k2_xboole_0 @ 
% 0.38/0.61              (k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 0.38/0.61              (k1_tarski @ X27)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.61         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.38/0.61           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.38/0.61              (k1_tarski @ X4)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.38/0.61         ((k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.38/0.61           = (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.38/0.61      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.61         ((k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.38/0.61           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.38/0.61              (k1_tarski @ X4)))),
% 0.38/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         ((k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.38/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '25'])).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.61         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.61           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['19', '20'])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.38/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.61         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.38/0.61           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (((k1_enumset1 @ sk_B @ sk_C @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '28', '29'])).
% 0.38/0.61  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.61  thf(zf_stmt_3, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.61       ( ![E:$i]:
% 0.38/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.61         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.38/0.61          | (r2_hidden @ X13 @ X17)
% 0.38/0.61          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.61         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.38/0.61          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.38/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.38/0.62          | (zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['30', '32'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.62         (((X9) != (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X10 @ X10 @ X11 @ X8)),
% 0.38/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.62  thf('36', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['33', '35'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X29 : $i, X30 : $i]:
% 0.38/0.62         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.38/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X18 @ X17)
% 0.38/0.62          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.38/0.62          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.38/0.62         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.38/0.62          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.62          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.38/0.62      inference('sup-', [status(thm)], ['37', '39'])).
% 0.38/0.62  thf('41', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.38/0.62      inference('sup-', [status(thm)], ['36', '40'])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '41'])).
% 0.38/0.62  thf('43', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.38/0.62      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.62  thf('44', plain, (((sk_A) != (sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.62  thf('45', plain, (((sk_A) != (sk_C))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.62  thf('46', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['43', '44', '45'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
