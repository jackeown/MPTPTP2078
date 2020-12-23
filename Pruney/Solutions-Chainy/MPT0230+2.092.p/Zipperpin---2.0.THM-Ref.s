%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FoJt90KJq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:20 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 116 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  805 ( 987 expanded)
%              Number of equality atoms :   80 ( 103 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
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
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
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
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','23'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('28',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k6_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k5_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('29',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('31',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('38',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('44',plain,
    ( ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['24','42','43'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X14 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FoJt90KJq
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 194 iterations in 0.124s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.40/0.58                                           $i > $i).
% 0.40/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(d1_enumset1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.58       ( ![E:$i]:
% 0.40/0.58         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, axiom,
% 0.40/0.58    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.40/0.58          | ((X13) = (X14))
% 0.40/0.58          | ((X13) = (X15))
% 0.40/0.58          | ((X13) = (X16)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t25_zfmisc_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.40/0.58          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_1, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.58        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.40/0.58             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.58  thf(t28_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.40/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.40/0.58         = (k1_tarski @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf(t100_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X3 @ X4)
% 0.40/0.58           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.40/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['3', '4'])).
% 0.40/0.58  thf(t92_xboole_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('6', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.40/0.58         = (k1_xboole_0))),
% 0.40/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf(t98_xboole_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ X10 @ X11)
% 0.40/0.58           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.40/0.58         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.40/0.58  thf(d10_xboole_0, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.40/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.58  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i]:
% 0.40/0.58         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.40/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.58  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         ((k4_xboole_0 @ X3 @ X4)
% 0.40/0.58           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf('16', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.40/0.58  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X10 : $i, X11 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ X10 @ X11)
% 0.40/0.58           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.58  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.40/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.59  thf(t12_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X5 : $i, X6 : $i]:
% 0.40/0.59         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.59  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.59  thf('23', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['19', '22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.40/0.59         = (k2_tarski @ sk_B @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['9', '23'])).
% 0.40/0.59  thf(t71_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 0.40/0.59           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.40/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.59  thf(t70_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X33 : $i, X34 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['25', '26'])).
% 0.40/0.59  thf(t75_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.40/0.59     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.40/0.59       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.40/0.59  thf('28', plain,
% 0.40/0.59      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 0.40/0.59         ((k6_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59)
% 0.40/0.59           = (k5_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 0.40/0.59      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.40/0.59  thf(t74_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.59     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.40/0.59       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.40/0.59         ((k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.40/0.59           = (k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52))),
% 0.40/0.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.40/0.59         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.59           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.40/0.59  thf(t73_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.40/0.59     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.40/0.59       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.40/0.59         ((k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.40/0.59           = (k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 0.40/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.59         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.59           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.40/0.59         ((k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.40/0.59           = (k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52))),
% 0.40/0.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.40/0.59  thf(t68_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.40/0.59     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.40/0.59       ( k2_xboole_0 @
% 0.40/0.59         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.40/0.59         X31 : $i]:
% 0.40/0.59         ((k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.40/0.59           = (k2_xboole_0 @ 
% 0.40/0.59              (k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30) @ 
% 0.40/0.59              (k1_tarski @ X31)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.40/0.59         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.40/0.59           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.40/0.59              (k1_tarski @ X6)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['33', '34'])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.59         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.59           = (k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.40/0.59              (k1_tarski @ X0)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['32', '35'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.40/0.59         ((k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46)
% 0.40/0.59           = (k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 0.40/0.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.40/0.59  thf(t72_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.59         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 0.40/0.59           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 0.40/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.59         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.40/0.59           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.40/0.59              (k1_tarski @ X0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.40/0.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.40/0.59      inference('sup+', [status(thm)], ['27', '39'])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.59         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 0.40/0.59           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 0.40/0.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.40/0.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.40/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.40/0.59         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 0.40/0.59           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.40/0.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (((k1_enumset1 @ sk_B @ sk_C @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.40/0.59      inference('demod', [status(thm)], ['24', '42', '43'])).
% 0.40/0.59  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.59  thf(zf_stmt_3, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.59       ( ![E:$i]:
% 0.40/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.59         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.40/0.59          | (r2_hidden @ X17 @ X21)
% 0.40/0.59          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.59         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.40/0.59          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.40/0.59      inference('simplify', [status(thm)], ['45'])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.40/0.59          | (zip_tseitin_0 @ X0 @ sk_A @ sk_C @ sk_B))),
% 0.40/0.59      inference('sup+', [status(thm)], ['44', '46'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.59         (((X13) != (X14)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('49', plain,
% 0.40/0.59      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.40/0.59         ~ (zip_tseitin_0 @ X14 @ X14 @ X15 @ X12)),
% 0.40/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.40/0.59  thf('50', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['47', '49'])).
% 0.40/0.59  thf('51', plain,
% 0.40/0.59      (![X33 : $i, X34 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf('52', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X22 @ X21)
% 0.40/0.59          | ~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.40/0.59          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.40/0.59         (~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.40/0.59          | ~ (r2_hidden @ X22 @ (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.59      inference('sup-', [status(thm)], ['51', '53'])).
% 0.40/0.59  thf('55', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.40/0.59      inference('sup-', [status(thm)], ['50', '54'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['0', '55'])).
% 0.40/0.59  thf('57', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.40/0.59  thf('58', plain, (((sk_A) != (sk_B))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.59  thf('59', plain, (((sk_A) != (sk_C))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.59  thf('60', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['57', '58', '59'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
