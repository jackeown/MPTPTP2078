%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CukROhLMqE

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:37 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   82 (  92 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  691 ( 799 expanded)
%              Number of equality atoms :   67 (  79 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('14',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k6_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k5_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('15',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('21',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','25'])).

thf('27',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['8','31'])).

thf('33',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X8 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CukROhLMqE
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.82/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.82/1.04  % Solved by: fo/fo7.sh
% 0.82/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.04  % done 902 iterations in 0.594s
% 0.82/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.82/1.04  % SZS output start Refutation
% 0.82/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.04  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.82/1.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.82/1.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.04  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.82/1.04  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.82/1.04                                           $i > $i).
% 0.82/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.04  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.82/1.04  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.82/1.04  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.82/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.04  thf(t18_zfmisc_1, conjecture,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.82/1.04         ( k1_tarski @ A ) ) =>
% 0.82/1.04       ( ( A ) = ( B ) ) ))).
% 0.82/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.04    (~( ![A:$i,B:$i]:
% 0.82/1.04        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.82/1.04            ( k1_tarski @ A ) ) =>
% 0.82/1.04          ( ( A ) = ( B ) ) ) )),
% 0.82/1.04    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.82/1.04  thf('0', plain,
% 0.82/1.04      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.82/1.04         = (k1_tarski @ sk_A))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf(t100_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.82/1.04  thf('1', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X0 @ X1)
% 0.82/1.04           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.82/1.04  thf('2', plain,
% 0.82/1.04      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.82/1.04         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['0', '1'])).
% 0.82/1.04  thf(t92_xboole_1, axiom,
% 0.82/1.04    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.82/1.04  thf('3', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.82/1.04  thf('4', plain,
% 0.82/1.04      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.82/1.04      inference('demod', [status(thm)], ['2', '3'])).
% 0.82/1.04  thf(t98_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.82/1.04  thf('5', plain,
% 0.82/1.04      (![X4 : $i, X5 : $i]:
% 0.82/1.04         ((k2_xboole_0 @ X4 @ X5)
% 0.82/1.04           = (k5_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.82/1.04  thf('6', plain,
% 0.82/1.04      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.82/1.04         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['4', '5'])).
% 0.82/1.04  thf(t5_boole, axiom,
% 0.82/1.04    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.82/1.04  thf('7', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.82/1.04      inference('cnf', [status(esa)], [t5_boole])).
% 0.82/1.04  thf('8', plain,
% 0.82/1.04      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.82/1.04         = (k1_tarski @ sk_B))),
% 0.82/1.04      inference('demod', [status(thm)], ['6', '7'])).
% 0.82/1.04  thf(t69_enumset1, axiom,
% 0.82/1.04    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.82/1.04  thf('9', plain, (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.82/1.04      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.04  thf(t71_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.82/1.04  thf('10', plain,
% 0.82/1.04      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.82/1.04         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.82/1.04           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.82/1.04      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.82/1.04  thf(t70_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.82/1.04  thf('11', plain,
% 0.82/1.04      (![X35 : $i, X36 : $i]:
% 0.82/1.04         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.82/1.04      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.04  thf('12', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['10', '11'])).
% 0.82/1.04  thf(t72_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.04     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.82/1.04  thf('13', plain,
% 0.82/1.04      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.82/1.04         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 0.82/1.04           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 0.82/1.04      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.82/1.04  thf(t75_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.82/1.04     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.82/1.04       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.82/1.04  thf('14', plain,
% 0.82/1.04      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.82/1.04         ((k6_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61)
% 0.82/1.04           = (k5_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 0.82/1.04      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.82/1.04  thf(t74_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.82/1.04     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.82/1.04       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.82/1.04  thf('15', plain,
% 0.82/1.04      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.82/1.04         ((k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.82/1.04           = (k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.82/1.04      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.82/1.04  thf('16', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.82/1.04         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.82/1.04           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['14', '15'])).
% 0.82/1.04  thf('17', plain,
% 0.82/1.04      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.82/1.04         ((k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.82/1.04           = (k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.82/1.04      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.82/1.04  thf(t68_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.82/1.04     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.82/1.04       ( k2_xboole_0 @
% 0.82/1.04         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.82/1.04  thf('18', plain,
% 0.82/1.04      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, 
% 0.82/1.04         X33 : $i]:
% 0.82/1.04         ((k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.82/1.04           = (k2_xboole_0 @ 
% 0.82/1.04              (k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32) @ 
% 0.82/1.04              (k1_tarski @ X33)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.82/1.04  thf('19', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.82/1.04         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.82/1.04           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.82/1.04              (k1_tarski @ X6)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['17', '18'])).
% 0.82/1.04  thf('20', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.82/1.04         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.82/1.04           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.82/1.04              (k1_tarski @ X0)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['16', '19'])).
% 0.82/1.04  thf(t73_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.82/1.04     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.82/1.04       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.82/1.04  thf('21', plain,
% 0.82/1.04      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.82/1.04         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.82/1.04           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.82/1.04      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.82/1.04  thf('22', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.82/1.04         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.82/1.04           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.82/1.04              (k1_tarski @ X0)))),
% 0.82/1.04      inference('demod', [status(thm)], ['20', '21'])).
% 0.82/1.04  thf('23', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.04         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.82/1.04           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.82/1.04              (k1_tarski @ X4)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['13', '22'])).
% 0.82/1.04  thf('24', plain,
% 0.82/1.04      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.82/1.04         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.82/1.04           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.82/1.04      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.82/1.04  thf('25', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.04         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.82/1.04           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.82/1.04              (k1_tarski @ X4)))),
% 0.82/1.04      inference('demod', [status(thm)], ['23', '24'])).
% 0.82/1.04  thf('26', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.82/1.04           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['12', '25'])).
% 0.82/1.04  thf('27', plain,
% 0.82/1.04      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.82/1.04         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 0.82/1.04           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 0.82/1.04      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.82/1.04  thf('28', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.82/1.04           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.82/1.04      inference('demod', [status(thm)], ['26', '27'])).
% 0.82/1.04  thf('29', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.82/1.04           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['9', '28'])).
% 0.82/1.04  thf('30', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['10', '11'])).
% 0.82/1.04  thf('31', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k2_tarski @ X0 @ X1)
% 0.82/1.04           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.82/1.04      inference('demod', [status(thm)], ['29', '30'])).
% 0.82/1.04  thf('32', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.82/1.04      inference('demod', [status(thm)], ['8', '31'])).
% 0.82/1.04  thf('33', plain,
% 0.82/1.04      (![X35 : $i, X36 : $i]:
% 0.82/1.04         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.82/1.04      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.04  thf(d1_enumset1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.04     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.04       ( ![E:$i]:
% 0.82/1.04         ( ( r2_hidden @ E @ D ) <=>
% 0.82/1.04           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.82/1.04  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.82/1.04  thf(zf_stmt_2, axiom,
% 0.82/1.04    (![E:$i,C:$i,B:$i,A:$i]:
% 0.82/1.04     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.82/1.04       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.82/1.04  thf(zf_stmt_3, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.04     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.04       ( ![E:$i]:
% 0.82/1.04         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.82/1.04  thf('34', plain,
% 0.82/1.04      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.82/1.04         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.82/1.04          | (r2_hidden @ X11 @ X15)
% 0.82/1.04          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.04  thf('35', plain,
% 0.82/1.04      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.82/1.04         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.82/1.04          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.82/1.04      inference('simplify', [status(thm)], ['34'])).
% 0.82/1.04  thf('36', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.82/1.04          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.82/1.04      inference('sup+', [status(thm)], ['33', '35'])).
% 0.82/1.04  thf('37', plain,
% 0.82/1.04      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.82/1.04         (((X7) != (X8)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.04  thf('38', plain,
% 0.82/1.04      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X8 @ X8 @ X9 @ X6)),
% 0.82/1.04      inference('simplify', [status(thm)], ['37'])).
% 0.82/1.04  thf('39', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.82/1.04      inference('sup-', [status(thm)], ['36', '38'])).
% 0.82/1.04  thf('40', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.82/1.04      inference('sup+', [status(thm)], ['32', '39'])).
% 0.82/1.04  thf(d1_tarski, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.82/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.82/1.04  thf('41', plain,
% 0.82/1.04      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X21 @ X20)
% 0.82/1.04          | ((X21) = (X18))
% 0.82/1.04          | ((X20) != (k1_tarski @ X18)))),
% 0.82/1.04      inference('cnf', [status(esa)], [d1_tarski])).
% 0.82/1.04  thf('42', plain,
% 0.82/1.04      (![X18 : $i, X21 : $i]:
% 0.82/1.04         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.82/1.04      inference('simplify', [status(thm)], ['41'])).
% 0.82/1.04  thf('43', plain, (((sk_A) = (sk_B))),
% 0.82/1.04      inference('sup-', [status(thm)], ['40', '42'])).
% 0.82/1.04  thf('44', plain, (((sk_A) != (sk_B))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('45', plain, ($false),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.82/1.04  
% 0.82/1.04  % SZS output end Refutation
% 0.82/1.04  
% 0.82/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
