%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N0Kvac4BSO

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:45 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   76 (  87 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  649 ( 848 expanded)
%              Number of equality atoms :   48 (  65 expanded)
%              Maximal formula depth    :   23 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t14_ordinal1,conjecture,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( A
       != ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t14_ordinal1])).

thf('0',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X54: $i] :
      ( ( k1_ordinal1 @ X54 )
      = ( k2_xboole_0 @ X54 @ ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      | ( r2_hidden @ X42 @ X51 )
      | ( X51
       != ( k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( r2_hidden @ X42 @ ( k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43 ) )
      | ( zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X33 != X34 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X32: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ~ ( zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X6 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','17'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ ( k3_tarski @ X29 ) )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_A ),
    inference('sup+',[status(thm)],['0','23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('33',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( X33 != X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X32: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ~ ( zip_tseitin_0 @ X32 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r2_hidden @ X55 @ X56 )
      | ~ ( r1_tarski @ X56 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( r1_tarski @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( r1_tarski @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X3 ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X2 ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    $false ),
    inference('sup-',[status(thm)],['24','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N0Kvac4BSO
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 214 iterations in 0.142s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.42/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.60  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.42/0.60  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.42/0.60                                           $i > $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.42/0.60                                               $i > $i > $i > $o).
% 0.42/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.42/0.60  thf(t14_ordinal1, conjecture, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t14_ordinal1])).
% 0.42/0.60  thf('0', plain, (((sk_A) = (k1_ordinal1 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(d1_ordinal1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X54 : $i]:
% 0.42/0.60         ((k1_ordinal1 @ X54) = (k2_xboole_0 @ X54 @ (k1_tarski @ X54)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.42/0.60  thf(t70_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X1 : $i, X2 : $i]:
% 0.42/0.60         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.60  thf(t71_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.60         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.42/0.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.60  thf(t72_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.42/0.60           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.42/0.60      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.42/0.60  thf(t73_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.42/0.60     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.42/0.60       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.60         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.42/0.60           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.42/0.60      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.42/0.60  thf(t74_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.60     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.42/0.60       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.60         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.42/0.60           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.42/0.60      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.42/0.60  thf(t75_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.60     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.42/0.60       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.42/0.60         ((k6_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.42/0.60           = (k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.42/0.60      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.42/0.60  thf(d6_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.42/0.60     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.42/0.60       ( ![J:$i]:
% 0.42/0.60         ( ( r2_hidden @ J @ I ) <=>
% 0.42/0.60           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.42/0.60                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.42/0.60                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.42/0.60      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_2, axiom,
% 0.42/0.60    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.42/0.60       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.42/0.60         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.42/0.60         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_3, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.42/0.60     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.42/0.60       ( ![J:$i]:
% 0.42/0.60         ( ( r2_hidden @ J @ I ) <=>
% 0.42/0.60           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.42/0.60         X49 : $i, X50 : $i, X51 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.42/0.60          | (r2_hidden @ X42 @ X51)
% 0.42/0.60          | ((X51)
% 0.42/0.60              != (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, 
% 0.42/0.60         X49 : $i, X50 : $i]:
% 0.42/0.60         ((r2_hidden @ X42 @ 
% 0.42/0.60           (k6_enumset1 @ X50 @ X49 @ X48 @ X47 @ X46 @ X45 @ X44 @ X43))
% 0.42/0.60          | (zip_tseitin_0 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 @ 
% 0.42/0.60             X50))),
% 0.42/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.60         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.42/0.60          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.42/0.60      inference('sup+', [status(thm)], ['7', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.42/0.60         X39 : $i, X40 : $i]:
% 0.42/0.60         (((X33) != (X34))
% 0.42/0.60          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 0.42/0.60               X32))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.42/0.60         X40 : $i]:
% 0.42/0.60         ~ (zip_tseitin_0 @ X34 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32)),
% 0.42/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.60         (r2_hidden @ X6 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.60         (r2_hidden @ X0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['6', '13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         (r2_hidden @ X0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['5', '14'])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.60         (r2_hidden @ X0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['4', '15'])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['3', '16'])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['2', '17'])).
% 0.42/0.60  thf(l49_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X28 : $i, X29 : $i]:
% 0.42/0.60         ((r1_tarski @ X28 @ (k3_tarski @ X29)) | ~ (r2_hidden @ X28 @ X29))),
% 0.42/0.60      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.60  thf(t93_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X30 : $i, X31 : $i]:
% 0.42/0.60         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 0.42/0.60      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['1', '22'])).
% 0.42/0.60  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_A)),
% 0.42/0.60      inference('sup+', [status(thm)], ['0', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X1 : $i, X2 : $i]:
% 0.42/0.60         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.60  thf(t69_enumset1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.60  thf('26', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['25', '26'])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.60         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.42/0.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.42/0.60  thf('29', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.60         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.42/0.60           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.42/0.60      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.60         ((k4_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.42/0.60           = (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.42/0.60      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.60         ((k5_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.42/0.60           = (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20))),
% 0.42/0.60      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.60         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.42/0.60          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.42/0.60      inference('sup+', [status(thm)], ['7', '9'])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.42/0.60         X39 : $i, X40 : $i]:
% 0.42/0.60         (((X33) != (X32))
% 0.42/0.60          | ~ (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ 
% 0.42/0.60               X32))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (![X32 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, 
% 0.42/0.60         X40 : $i]:
% 0.42/0.60         ~ (zip_tseitin_0 @ X32 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X32)),
% 0.42/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.60         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.42/0.60      inference('sup-', [status(thm)], ['32', '34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.60         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['31', '35'])).
% 0.42/0.60  thf(t7_ordinal1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X55 : $i, X56 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X55 @ X56) | ~ (r1_tarski @ X56 @ X55))),
% 0.42/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.60         ~ (r1_tarski @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)),
% 0.42/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.60         ~ (r1_tarski @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X4)),
% 0.42/0.60      inference('sup-', [status(thm)], ['30', '38'])).
% 0.42/0.60  thf('40', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.60         ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X3)),
% 0.42/0.60      inference('sup-', [status(thm)], ['29', '39'])).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X2)),
% 0.42/0.60      inference('sup-', [status(thm)], ['28', '40'])).
% 0.42/0.60  thf('42', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.42/0.60      inference('sup-', [status(thm)], ['27', '41'])).
% 0.42/0.60  thf('43', plain, ($false), inference('sup-', [status(thm)], ['24', '42'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
