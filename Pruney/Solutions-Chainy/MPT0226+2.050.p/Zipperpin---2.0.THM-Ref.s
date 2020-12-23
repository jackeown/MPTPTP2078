%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BFRea08Bgo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:57 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   77 (  95 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  642 ( 838 expanded)
%              Number of equality atoms :   61 (  83 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( X6 = X7 )
      | ( X6 = X8 )
      | ( X6 = X9 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
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
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
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
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('7',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k4_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 @ X58 )
      = ( k3_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('8',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k3_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_enumset1 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( k2_enumset1 @ X47 @ X47 @ X48 @ X49 )
      = ( k1_enumset1 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('14',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( k5_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 )
      = ( k4_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k6_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('18',plain,(
    ! [X65: $i,X66: $i,X67: $i,X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ( k6_enumset1 @ X65 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 )
      = ( k5_enumset1 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('19',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ( k5_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 )
      = ( k4_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['5','24'])).

thf('26',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
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

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BFRea08Bgo
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:09:19 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 411 iterations in 0.144s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.42/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.42/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.62  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.42/0.62                                           $i > $i).
% 0.42/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(d1_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.62       ( ![E:$i]:
% 0.42/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.42/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, axiom,
% 0.42/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.42/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.42/0.62          | ((X6) = (X7))
% 0.42/0.62          | ((X6) = (X8))
% 0.42/0.62          | ((X6) = (X9)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t21_zfmisc_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.42/0.62         ( k1_xboole_0 ) ) =>
% 0.42/0.62       ( ( A ) = ( B ) ) ))).
% 0.42/0.62  thf(zf_stmt_1, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.42/0.62            ( k1_xboole_0 ) ) =>
% 0.42/0.62          ( ( A ) = ( B ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.62  thf(t98_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i]:
% 0.42/0.62         ((k2_xboole_0 @ X3 @ X4)
% 0.42/0.62           = (k5_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.42/0.62         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf(t5_boole, axiom,
% 0.42/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.62  thf('4', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.42/0.62         = (k1_tarski @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf(t69_enumset1, axiom,
% 0.42/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.62  thf('6', plain, (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf(t73_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.42/0.62     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.42/0.62       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.42/0.62         ((k4_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 @ X58)
% 0.42/0.62           = (k3_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58))),
% 0.42/0.62      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.42/0.62  thf(t72_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.42/0.62         ((k3_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53)
% 0.42/0.62           = (k2_enumset1 @ X50 @ X51 @ X52 @ X53))),
% 0.42/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.42/0.62           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.42/0.62  thf(t71_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X47 @ X47 @ X48 @ X49)
% 0.42/0.62           = (k1_enumset1 @ X47 @ X48 @ X49))),
% 0.42/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.62  thf(t70_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X45 : $i, X46 : $i]:
% 0.42/0.62         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.42/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['9', '12'])).
% 0.42/0.62  thf(t74_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.62     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.42/0.62       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 0.42/0.62         ((k5_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64)
% 0.42/0.62           = (k4_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64))),
% 0.42/0.62      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.42/0.62  thf(t68_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.42/0.62     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.42/0.62       ( k2_xboole_0 @
% 0.42/0.62         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 0.42/0.62         X43 : $i]:
% 0.42/0.62         ((k6_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.42/0.62           = (k2_xboole_0 @ 
% 0.42/0.62              (k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42) @ 
% 0.42/0.62              (k1_tarski @ X43)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.62         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.42/0.62           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.42/0.62              (k1_tarski @ X6)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.42/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['13', '16'])).
% 0.42/0.62  thf(t75_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.62     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.42/0.62       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X65 : $i, X66 : $i, X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i]:
% 0.42/0.62         ((k6_enumset1 @ X65 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71)
% 0.42/0.62           = (k5_enumset1 @ X65 @ X66 @ X67 @ X68 @ X69 @ X70 @ X71))),
% 0.42/0.62      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 0.42/0.62         ((k5_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64)
% 0.42/0.62           = (k4_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63 @ X64))),
% 0.42/0.62      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.62         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.42/0.62           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.42/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.42/0.62      inference('demod', [status(thm)], ['17', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.42/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['6', '21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['9', '12'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k2_tarski @ X0 @ X1)
% 0.42/0.62           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.42/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('25', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['5', '24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X45 : $i, X46 : $i]:
% 0.42/0.62         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.42/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.62  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_3, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.62       ( ![E:$i]:
% 0.42/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.42/0.62          | (r2_hidden @ X10 @ X14)
% 0.42/0.62          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.62         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.42/0.62          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.42/0.62      inference('simplify', [status(thm)], ['27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.62          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.42/0.62      inference('sup+', [status(thm)], ['26', '28'])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.62         (((X6) != (X7)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X7 @ X7 @ X8 @ X5)),
% 0.42/0.62      inference('simplify', [status(thm)], ['30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '31'])).
% 0.42/0.62  thf('33', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['25', '32'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X45 : $i, X46 : $i]:
% 0.42/0.62         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.42/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X15 @ X14)
% 0.42/0.62          | ~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.42/0.62          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.42/0.62         (~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.42/0.62          | ~ (r2_hidden @ X15 @ (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.42/0.62          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['34', '38'])).
% 0.42/0.62  thf('40', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.42/0.62      inference('sup-', [status(thm)], ['33', '39'])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '40'])).
% 0.42/0.62  thf('42', plain, (((sk_A) = (sk_B))),
% 0.42/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.42/0.62  thf('43', plain, (((sk_A) != (sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.62  thf('44', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
