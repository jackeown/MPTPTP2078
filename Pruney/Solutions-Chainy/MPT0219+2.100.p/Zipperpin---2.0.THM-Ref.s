%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rAQDJEfNo6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:16 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   71 (  85 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  640 ( 790 expanded)
%              Number of equality atoms :   58 (  76 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k2_enumset1 @ X32 @ X32 @ X33 @ X34 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('6',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k6_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 )
      = ( k5_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('7',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k5_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k4_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('9',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k5_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k4_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_enumset1 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['1','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X11 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','39'])).

thf('41',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rAQDJEfNo6
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:44:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.30/1.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.30/1.50  % Solved by: fo/fo7.sh
% 1.30/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.50  % done 344 iterations in 1.002s
% 1.30/1.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.30/1.50  % SZS output start Refutation
% 1.30/1.50  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.30/1.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.30/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.30/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.30/1.50  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.30/1.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.30/1.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.50  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.30/1.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.30/1.50  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.30/1.50                                           $i > $i).
% 1.30/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.30/1.50  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.30/1.50  thf(d1_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.30/1.50       ( ![E:$i]:
% 1.30/1.50         ( ( r2_hidden @ E @ D ) <=>
% 1.30/1.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.30/1.50  thf(zf_stmt_0, axiom,
% 1.30/1.50    (![E:$i,C:$i,B:$i,A:$i]:
% 1.30/1.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.30/1.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.30/1.50  thf('0', plain,
% 1.30/1.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.30/1.50         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 1.30/1.50          | ((X10) = (X11))
% 1.30/1.50          | ((X10) = (X12))
% 1.30/1.50          | ((X10) = (X13)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf(t13_zfmisc_1, conjecture,
% 1.30/1.50    (![A:$i,B:$i]:
% 1.30/1.50     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.30/1.50         ( k1_tarski @ A ) ) =>
% 1.30/1.50       ( ( A ) = ( B ) ) ))).
% 1.30/1.50  thf(zf_stmt_1, negated_conjecture,
% 1.30/1.50    (~( ![A:$i,B:$i]:
% 1.30/1.50        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.30/1.50            ( k1_tarski @ A ) ) =>
% 1.30/1.50          ( ( A ) = ( B ) ) ) )),
% 1.30/1.50    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 1.30/1.50  thf('1', plain,
% 1.30/1.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.30/1.50         = (k1_tarski @ sk_A))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.30/1.50  thf(t69_enumset1, axiom,
% 1.30/1.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.30/1.50  thf('2', plain, (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 1.30/1.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.30/1.50  thf(t71_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i]:
% 1.30/1.50     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.30/1.50  thf('3', plain,
% 1.30/1.50      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.30/1.50         ((k2_enumset1 @ X32 @ X32 @ X33 @ X34)
% 1.30/1.50           = (k1_enumset1 @ X32 @ X33 @ X34))),
% 1.30/1.50      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.30/1.50  thf(t70_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.30/1.50  thf('4', plain,
% 1.30/1.50      (![X30 : $i, X31 : $i]:
% 1.30/1.50         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 1.30/1.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.30/1.50  thf('5', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['3', '4'])).
% 1.30/1.50  thf(t75_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.30/1.50     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.30/1.50       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.30/1.50  thf('6', plain,
% 1.30/1.50      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 1.30/1.50         ((k6_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56)
% 1.30/1.50           = (k5_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56))),
% 1.30/1.50      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.30/1.50  thf(t74_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.30/1.50     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.30/1.50       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.30/1.50  thf('7', plain,
% 1.30/1.50      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.30/1.50         ((k5_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 1.30/1.50           = (k4_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 1.30/1.50      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.30/1.50  thf('8', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.30/1.50         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.30/1.50           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['6', '7'])).
% 1.30/1.50  thf(t73_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.30/1.50     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.30/1.50       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.30/1.50  thf('9', plain,
% 1.30/1.50      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.30/1.50         ((k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43)
% 1.30/1.50           = (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 1.30/1.50      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.30/1.50  thf('10', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.30/1.50         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.30/1.50           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['8', '9'])).
% 1.30/1.50  thf(t72_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.50     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.30/1.50  thf('11', plain,
% 1.30/1.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.30/1.50         ((k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38)
% 1.30/1.50           = (k2_enumset1 @ X35 @ X36 @ X37 @ X38))),
% 1.30/1.50      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.30/1.50  thf('12', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.50         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.30/1.50           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['10', '11'])).
% 1.30/1.50  thf('13', plain,
% 1.30/1.50      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.30/1.50         ((k5_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 1.30/1.50           = (k4_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 1.30/1.50      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.30/1.50  thf(t68_enumset1, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.30/1.50     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.30/1.50       ( k2_xboole_0 @
% 1.30/1.50         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 1.30/1.50  thf('14', plain,
% 1.30/1.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 1.30/1.50         X28 : $i]:
% 1.30/1.50         ((k6_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 1.30/1.50           = (k2_xboole_0 @ 
% 1.30/1.50              (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27) @ 
% 1.30/1.50              (k1_tarski @ X28)))),
% 1.30/1.50      inference('cnf', [status(esa)], [t68_enumset1])).
% 1.30/1.50  thf('15', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.30/1.50         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 1.30/1.50           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 1.30/1.50              (k1_tarski @ X6)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['13', '14'])).
% 1.30/1.50  thf('16', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.50         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.30/1.50           = (k2_xboole_0 @ (k4_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1) @ 
% 1.30/1.50              (k1_tarski @ X0)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['12', '15'])).
% 1.30/1.50  thf('17', plain,
% 1.30/1.50      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.30/1.50         ((k4_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43)
% 1.30/1.50           = (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 1.30/1.50      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.30/1.50  thf('18', plain,
% 1.30/1.50      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.30/1.50         ((k3_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38)
% 1.30/1.50           = (k2_enumset1 @ X35 @ X36 @ X37 @ X38))),
% 1.30/1.50      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.30/1.50  thf('19', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.30/1.50         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 1.30/1.50           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ 
% 1.30/1.50              (k1_tarski @ X0)))),
% 1.30/1.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.30/1.50  thf('20', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.30/1.50           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['5', '19'])).
% 1.30/1.50  thf('21', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 1.30/1.50           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.30/1.50      inference('sup+', [status(thm)], ['2', '20'])).
% 1.30/1.50  thf('22', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.30/1.50      inference('sup+', [status(thm)], ['3', '4'])).
% 1.30/1.50  thf('23', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         ((k2_tarski @ X0 @ X1)
% 1.30/1.50           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.30/1.50      inference('demod', [status(thm)], ['21', '22'])).
% 1.30/1.50  thf('24', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 1.30/1.50      inference('demod', [status(thm)], ['1', '23'])).
% 1.30/1.50  thf('25', plain,
% 1.30/1.50      (![X30 : $i, X31 : $i]:
% 1.30/1.50         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 1.30/1.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.30/1.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.30/1.50  thf(zf_stmt_3, axiom,
% 1.30/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.30/1.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.30/1.50       ( ![E:$i]:
% 1.30/1.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.30/1.50  thf('26', plain,
% 1.30/1.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.30/1.50         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 1.30/1.50          | (r2_hidden @ X14 @ X18)
% 1.30/1.50          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.30/1.50  thf('27', plain,
% 1.30/1.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.30/1.50         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 1.30/1.50          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 1.30/1.50      inference('simplify', [status(thm)], ['26'])).
% 1.30/1.50  thf('28', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.30/1.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.30/1.50      inference('sup+', [status(thm)], ['25', '27'])).
% 1.30/1.50  thf('29', plain,
% 1.30/1.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.30/1.50         (((X10) != (X11)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.50  thf('30', plain,
% 1.30/1.50      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X11 @ X11 @ X12 @ X9)),
% 1.30/1.50      inference('simplify', [status(thm)], ['29'])).
% 1.30/1.50  thf('31', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.30/1.50      inference('sup-', [status(thm)], ['28', '30'])).
% 1.30/1.50  thf('32', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 1.30/1.50      inference('sup+', [status(thm)], ['24', '31'])).
% 1.30/1.50  thf('33', plain,
% 1.30/1.50      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 1.30/1.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.30/1.50  thf('34', plain,
% 1.30/1.50      (![X30 : $i, X31 : $i]:
% 1.30/1.50         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 1.30/1.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.30/1.50  thf('35', plain,
% 1.30/1.50      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.30/1.50         (~ (r2_hidden @ X19 @ X18)
% 1.30/1.50          | ~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 1.30/1.50          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.30/1.50  thf('36', plain,
% 1.30/1.50      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 1.30/1.50         (~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 1.30/1.50          | ~ (r2_hidden @ X19 @ (k1_enumset1 @ X17 @ X16 @ X15)))),
% 1.30/1.50      inference('simplify', [status(thm)], ['35'])).
% 1.30/1.50  thf('37', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.30/1.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.30/1.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.30/1.50      inference('sup-', [status(thm)], ['34', '36'])).
% 1.30/1.50  thf('38', plain,
% 1.30/1.50      (![X0 : $i, X1 : $i]:
% 1.30/1.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.30/1.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.30/1.50      inference('sup-', [status(thm)], ['33', '37'])).
% 1.30/1.50  thf('39', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 1.30/1.50      inference('sup-', [status(thm)], ['32', '38'])).
% 1.30/1.50  thf('40', plain,
% 1.30/1.50      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 1.30/1.50      inference('sup-', [status(thm)], ['0', '39'])).
% 1.30/1.50  thf('41', plain, (((sk_B) = (sk_A))),
% 1.30/1.50      inference('simplify', [status(thm)], ['40'])).
% 1.30/1.50  thf('42', plain, (((sk_A) != (sk_B))),
% 1.30/1.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.30/1.50  thf('43', plain, ($false),
% 1.30/1.50      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 1.30/1.50  
% 1.30/1.50  % SZS output end Refutation
% 1.30/1.50  
% 1.30/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
