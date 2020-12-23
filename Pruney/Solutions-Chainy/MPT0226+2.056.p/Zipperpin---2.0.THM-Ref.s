%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Ud7hcrKcH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:58 EST 2020

% Result     : Theorem 1.08s
% Output     : Refutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :   81 (  98 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  710 ( 906 expanded)
%              Number of equality atoms :   64 (  85 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X7 )
      | ( X4 = X5 )
      | ( X4 = X6 )
      | ( X4 = X7 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
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
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t78_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k3_enumset1 @ X55 @ X55 @ X55 @ X56 @ X57 )
      = ( k1_enumset1 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('8',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k2_enumset1 @ X55 @ X55 @ X56 @ X57 )
      = ( k1_enumset1 @ X55 @ X56 @ X57 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('14',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) @ ( k2_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('20',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t81_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('24',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k6_enumset1 @ X58 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 )
      = ( k4_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf('25',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('26',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k5_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 )
      = ( k4_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( k2_enumset1 @ X55 @ X55 @ X56 @ X57 )
      = ( k1_enumset1 @ X55 @ X56 @ X57 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 )
      | ( r2_hidden @ X8 @ X12 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X5 @ X6 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X5 @ X6 @ X3 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ( X12
       != ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X13 @ X9 @ X10 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_enumset1 @ X11 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Ud7hcrKcH
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.08/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.08/1.31  % Solved by: fo/fo7.sh
% 1.08/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.08/1.31  % done 1104 iterations in 0.857s
% 1.08/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.08/1.31  % SZS output start Refutation
% 1.08/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.08/1.31  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.08/1.31  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.08/1.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.08/1.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.08/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.08/1.31  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.08/1.31  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.08/1.31  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.08/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.08/1.31  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.08/1.31  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.08/1.31                                           $i > $i).
% 1.08/1.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.08/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.08/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.08/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.08/1.31  thf(d1_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.31     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.08/1.31       ( ![E:$i]:
% 1.08/1.31         ( ( r2_hidden @ E @ D ) <=>
% 1.08/1.31           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.08/1.31  thf(zf_stmt_0, axiom,
% 1.08/1.31    (![E:$i,C:$i,B:$i,A:$i]:
% 1.08/1.31     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.08/1.31       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.08/1.31  thf('0', plain,
% 1.08/1.31      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.08/1.31         ((zip_tseitin_0 @ X4 @ X5 @ X6 @ X7)
% 1.08/1.31          | ((X4) = (X5))
% 1.08/1.31          | ((X4) = (X6))
% 1.08/1.31          | ((X4) = (X7)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf(t21_zfmisc_1, conjecture,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.08/1.31         ( k1_xboole_0 ) ) =>
% 1.08/1.31       ( ( A ) = ( B ) ) ))).
% 1.08/1.31  thf(zf_stmt_1, negated_conjecture,
% 1.08/1.31    (~( ![A:$i,B:$i]:
% 1.08/1.31        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.08/1.31            ( k1_xboole_0 ) ) =>
% 1.08/1.31          ( ( A ) = ( B ) ) ) )),
% 1.08/1.31    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 1.08/1.31  thf('1', plain,
% 1.08/1.31      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.08/1.31  thf(t98_xboole_1, axiom,
% 1.08/1.31    (![A:$i,B:$i]:
% 1.08/1.31     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.08/1.31  thf('2', plain,
% 1.08/1.31      (![X1 : $i, X2 : $i]:
% 1.08/1.31         ((k2_xboole_0 @ X1 @ X2)
% 1.08/1.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.08/1.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.08/1.31  thf('3', plain,
% 1.08/1.31      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.08/1.31         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 1.08/1.31      inference('sup+', [status(thm)], ['1', '2'])).
% 1.08/1.31  thf(t5_boole, axiom,
% 1.08/1.31    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.08/1.31  thf('4', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.08/1.31      inference('cnf', [status(esa)], [t5_boole])).
% 1.08/1.31  thf('5', plain,
% 1.08/1.31      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.08/1.31         = (k1_tarski @ sk_B))),
% 1.08/1.31      inference('demod', [status(thm)], ['3', '4'])).
% 1.08/1.31  thf(t78_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i]:
% 1.08/1.31     ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.08/1.31  thf('6', plain,
% 1.08/1.31      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.08/1.31         ((k3_enumset1 @ X55 @ X55 @ X55 @ X56 @ X57)
% 1.08/1.31           = (k1_enumset1 @ X55 @ X56 @ X57))),
% 1.08/1.31      inference('cnf', [status(esa)], [t78_enumset1])).
% 1.08/1.31  thf(t72_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.31     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.08/1.31  thf('7', plain,
% 1.08/1.31      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.08/1.31         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.08/1.31           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.08/1.31      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.08/1.31  thf('8', plain,
% 1.08/1.31      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.08/1.31         ((k2_enumset1 @ X55 @ X55 @ X56 @ X57)
% 1.08/1.31           = (k1_enumset1 @ X55 @ X56 @ X57))),
% 1.08/1.31      inference('demod', [status(thm)], ['6', '7'])).
% 1.08/1.31  thf(t70_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.08/1.31  thf('9', plain,
% 1.08/1.31      (![X37 : $i, X38 : $i]:
% 1.08/1.31         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 1.08/1.31      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.08/1.31  thf('10', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i]:
% 1.08/1.31         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.08/1.31      inference('sup+', [status(thm)], ['8', '9'])).
% 1.08/1.31  thf(t69_enumset1, axiom,
% 1.08/1.31    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.08/1.31  thf('11', plain,
% 1.08/1.31      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.08/1.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.31  thf('12', plain,
% 1.08/1.31      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.08/1.31      inference('sup+', [status(thm)], ['10', '11'])).
% 1.08/1.31  thf(t73_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.08/1.31     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.08/1.31       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.08/1.31  thf('13', plain,
% 1.08/1.31      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.08/1.31         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 1.08/1.31           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 1.08/1.31      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.08/1.31  thf('14', plain,
% 1.08/1.31      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.08/1.31         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 1.08/1.31           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 1.08/1.31      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.08/1.31  thf('15', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.08/1.31         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.08/1.31           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.08/1.31      inference('sup+', [status(thm)], ['13', '14'])).
% 1.08/1.31  thf('16', plain,
% 1.08/1.31      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.08/1.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.31  thf(t67_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.08/1.31     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.08/1.31       ( k2_xboole_0 @
% 1.08/1.31         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 1.08/1.31  thf('17', plain,
% 1.08/1.31      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, 
% 1.08/1.31         X35 : $i]:
% 1.08/1.31         ((k6_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 1.08/1.31           = (k2_xboole_0 @ 
% 1.08/1.31              (k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33) @ 
% 1.08/1.31              (k2_tarski @ X34 @ X35)))),
% 1.08/1.31      inference('cnf', [status(esa)], [t67_enumset1])).
% 1.08/1.31  thf('18', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.08/1.31         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.08/1.31           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.08/1.31              (k1_tarski @ X0)))),
% 1.08/1.31      inference('sup+', [status(thm)], ['16', '17'])).
% 1.08/1.31  thf('19', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.08/1.31         ((k6_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X4)
% 1.08/1.31           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.08/1.31              (k1_tarski @ X4)))),
% 1.08/1.31      inference('sup+', [status(thm)], ['15', '18'])).
% 1.08/1.31  thf(t75_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.08/1.31     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.08/1.31       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.08/1.31  thf('20', plain,
% 1.08/1.31      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.08/1.31         ((k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 1.08/1.31           = (k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 1.08/1.31      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.08/1.31  thf('21', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.08/1.31         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 @ X4)
% 1.08/1.31           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.08/1.31              (k1_tarski @ X4)))),
% 1.08/1.31      inference('demod', [status(thm)], ['19', '20'])).
% 1.08/1.31  thf('22', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i]:
% 1.08/1.31         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 @ X1)
% 1.08/1.31           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.08/1.31      inference('sup+', [status(thm)], ['12', '21'])).
% 1.08/1.31  thf('23', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.08/1.31         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.08/1.31           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.08/1.31      inference('sup+', [status(thm)], ['13', '14'])).
% 1.08/1.31  thf(t81_enumset1, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.08/1.31     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 1.08/1.31       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.08/1.31  thf('24', plain,
% 1.08/1.31      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 1.08/1.31         ((k6_enumset1 @ X58 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63)
% 1.08/1.31           = (k4_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63))),
% 1.08/1.31      inference('cnf', [status(esa)], [t81_enumset1])).
% 1.08/1.31  thf('25', plain,
% 1.08/1.31      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.08/1.31         ((k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 1.08/1.31           = (k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 1.08/1.31      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.08/1.31  thf('26', plain,
% 1.08/1.31      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 1.08/1.31         ((k5_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63)
% 1.08/1.31           = (k4_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63))),
% 1.08/1.31      inference('demod', [status(thm)], ['24', '25'])).
% 1.08/1.31  thf('27', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.08/1.31         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.08/1.31           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.08/1.31      inference('sup+', [status(thm)], ['23', '26'])).
% 1.08/1.31  thf('28', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i]:
% 1.08/1.31         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1)
% 1.08/1.31           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.08/1.31      inference('demod', [status(thm)], ['22', '27'])).
% 1.08/1.31  thf('29', plain,
% 1.08/1.31      (![X55 : $i, X56 : $i, X57 : $i]:
% 1.08/1.31         ((k2_enumset1 @ X55 @ X55 @ X56 @ X57)
% 1.08/1.31           = (k1_enumset1 @ X55 @ X56 @ X57))),
% 1.08/1.31      inference('demod', [status(thm)], ['6', '7'])).
% 1.08/1.31  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.08/1.31  thf(zf_stmt_3, axiom,
% 1.08/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.08/1.31     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.08/1.31       ( ![E:$i]:
% 1.08/1.31         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.08/1.31  thf('30', plain,
% 1.08/1.31      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.08/1.31         ((zip_tseitin_0 @ X8 @ X9 @ X10 @ X11)
% 1.08/1.31          | (r2_hidden @ X8 @ X12)
% 1.08/1.31          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.08/1.31  thf('31', plain,
% 1.08/1.31      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.08/1.31         ((r2_hidden @ X8 @ (k1_enumset1 @ X11 @ X10 @ X9))
% 1.08/1.31          | (zip_tseitin_0 @ X8 @ X9 @ X10 @ X11))),
% 1.08/1.31      inference('simplify', [status(thm)], ['30'])).
% 1.08/1.31  thf('32', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.08/1.31         ((r2_hidden @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 1.08/1.31          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2))),
% 1.08/1.31      inference('sup+', [status(thm)], ['29', '31'])).
% 1.08/1.31  thf('33', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.08/1.31         ((r2_hidden @ X2 @ (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 1.08/1.31          | (zip_tseitin_0 @ X2 @ X0 @ X0 @ X1))),
% 1.08/1.31      inference('sup+', [status(thm)], ['28', '32'])).
% 1.08/1.31  thf('34', plain,
% 1.08/1.31      (![X0 : $i]:
% 1.08/1.31         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.08/1.31          | (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_B))),
% 1.08/1.31      inference('sup+', [status(thm)], ['5', '33'])).
% 1.08/1.31  thf('35', plain,
% 1.08/1.31      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.08/1.31         (((X4) != (X6)) | ~ (zip_tseitin_0 @ X4 @ X5 @ X6 @ X3))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.08/1.31  thf('36', plain,
% 1.08/1.31      (![X3 : $i, X5 : $i, X6 : $i]: ~ (zip_tseitin_0 @ X6 @ X5 @ X6 @ X3)),
% 1.08/1.31      inference('simplify', [status(thm)], ['35'])).
% 1.08/1.31  thf('37', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 1.08/1.31      inference('sup-', [status(thm)], ['34', '36'])).
% 1.08/1.31  thf('38', plain,
% 1.08/1.31      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.08/1.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.08/1.31  thf('39', plain,
% 1.08/1.31      (![X37 : $i, X38 : $i]:
% 1.08/1.31         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 1.08/1.31      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.08/1.31  thf('40', plain,
% 1.08/1.31      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.08/1.31         (~ (r2_hidden @ X13 @ X12)
% 1.08/1.31          | ~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 1.08/1.31          | ((X12) != (k1_enumset1 @ X11 @ X10 @ X9)))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.08/1.31  thf('41', plain,
% 1.08/1.31      (![X9 : $i, X10 : $i, X11 : $i, X13 : $i]:
% 1.08/1.31         (~ (zip_tseitin_0 @ X13 @ X9 @ X10 @ X11)
% 1.08/1.31          | ~ (r2_hidden @ X13 @ (k1_enumset1 @ X11 @ X10 @ X9)))),
% 1.08/1.31      inference('simplify', [status(thm)], ['40'])).
% 1.08/1.31  thf('42', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.08/1.31         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.08/1.31          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.08/1.31      inference('sup-', [status(thm)], ['39', '41'])).
% 1.08/1.31  thf('43', plain,
% 1.08/1.31      (![X0 : $i, X1 : $i]:
% 1.08/1.31         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.08/1.31          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.08/1.31      inference('sup-', [status(thm)], ['38', '42'])).
% 1.08/1.31  thf('44', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 1.08/1.31      inference('sup-', [status(thm)], ['37', '43'])).
% 1.08/1.31  thf('45', plain,
% 1.08/1.31      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 1.08/1.31      inference('sup-', [status(thm)], ['0', '44'])).
% 1.08/1.31  thf('46', plain, (((sk_A) = (sk_B))),
% 1.08/1.31      inference('simplify', [status(thm)], ['45'])).
% 1.08/1.31  thf('47', plain, (((sk_A) != (sk_B))),
% 1.08/1.31      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.08/1.31  thf('48', plain, ($false),
% 1.08/1.31      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 1.08/1.31  
% 1.08/1.31  % SZS output end Refutation
% 1.08/1.31  
% 1.16/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
