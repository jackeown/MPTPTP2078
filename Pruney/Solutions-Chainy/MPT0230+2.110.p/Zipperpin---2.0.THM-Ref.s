%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v3JfGO7ena

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:23 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 126 expanded)
%              Number of leaves         :   39 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :  749 ( 986 expanded)
%              Number of equality atoms :   80 ( 107 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( X17 = X18 )
      | ( X17 = X19 )
      | ( X17 = X20 ) ) ),
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
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','23','24'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('26',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('29',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_enumset1 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('33',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('34',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_enumset1 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X30 @ X29 @ X28 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('43',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X30 @ X29 @ X28 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('44',plain,
    ( ( k1_enumset1 @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','36','41','42','43'])).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_B_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,
    ( ( sk_A = sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_B_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v3JfGO7ena
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:22 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running portfolio for 600 s
% 0.21/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.16/1.36  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.16/1.36  % Solved by: fo/fo7.sh
% 1.16/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.36  % done 2588 iterations in 0.901s
% 1.16/1.36  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.16/1.36  % SZS output start Refutation
% 1.16/1.36  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.16/1.36  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.16/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.16/1.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.16/1.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.16/1.36  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.16/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.16/1.36  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.16/1.36  thf(sk_B_type, type, sk_B: $i > $i).
% 1.16/1.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.16/1.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.16/1.36  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.16/1.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.16/1.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.16/1.36  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.16/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.36  thf(d1_enumset1, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.16/1.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.16/1.36       ( ![E:$i]:
% 1.16/1.36         ( ( r2_hidden @ E @ D ) <=>
% 1.16/1.36           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.16/1.36  thf(zf_stmt_0, axiom,
% 1.16/1.36    (![E:$i,C:$i,B:$i,A:$i]:
% 1.16/1.36     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.16/1.36       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.16/1.36  thf('0', plain,
% 1.16/1.36      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.16/1.36         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 1.16/1.36          | ((X17) = (X18))
% 1.16/1.36          | ((X17) = (X19))
% 1.16/1.36          | ((X17) = (X20)))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.36  thf(t25_zfmisc_1, conjecture,
% 1.16/1.36    (![A:$i,B:$i,C:$i]:
% 1.16/1.36     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 1.16/1.36          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 1.16/1.36  thf(zf_stmt_1, negated_conjecture,
% 1.16/1.36    (~( ![A:$i,B:$i,C:$i]:
% 1.16/1.36        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 1.16/1.36             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 1.16/1.36    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 1.16/1.36  thf('1', plain,
% 1.16/1.36      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.36  thf(t28_xboole_1, axiom,
% 1.16/1.36    (![A:$i,B:$i]:
% 1.16/1.36     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.16/1.36  thf('2', plain,
% 1.16/1.36      (![X8 : $i, X9 : $i]:
% 1.16/1.36         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 1.16/1.36      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.16/1.36  thf('3', plain,
% 1.16/1.36      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 1.16/1.36         = (k1_tarski @ sk_A))),
% 1.16/1.36      inference('sup-', [status(thm)], ['1', '2'])).
% 1.16/1.36  thf(t100_xboole_1, axiom,
% 1.16/1.36    (![A:$i,B:$i]:
% 1.16/1.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.16/1.36  thf('4', plain,
% 1.16/1.36      (![X6 : $i, X7 : $i]:
% 1.16/1.36         ((k4_xboole_0 @ X6 @ X7)
% 1.16/1.36           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.16/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.16/1.36  thf('5', plain,
% 1.16/1.36      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 1.16/1.36         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.16/1.36      inference('sup+', [status(thm)], ['3', '4'])).
% 1.16/1.36  thf(t98_xboole_1, axiom,
% 1.16/1.36    (![A:$i,B:$i]:
% 1.16/1.36     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.16/1.36  thf('6', plain,
% 1.16/1.36      (![X14 : $i, X15 : $i]:
% 1.16/1.36         ((k2_xboole_0 @ X14 @ X15)
% 1.16/1.36           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.16/1.36      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.16/1.36  thf('7', plain,
% 1.16/1.36      (((k2_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 1.16/1.36         = (k5_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ 
% 1.16/1.36            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 1.16/1.36      inference('sup+', [status(thm)], ['5', '6'])).
% 1.16/1.36  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.16/1.36  thf('8', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 1.16/1.36      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.16/1.36  thf(t7_xboole_0, axiom,
% 1.16/1.36    (![A:$i]:
% 1.16/1.36     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.16/1.36          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.16/1.36  thf('9', plain,
% 1.16/1.36      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 1.16/1.36      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.16/1.36  thf(t4_xboole_0, axiom,
% 1.16/1.36    (![A:$i,B:$i]:
% 1.16/1.36     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.16/1.36            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.16/1.36       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.16/1.36            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.16/1.36  thf('10', plain,
% 1.16/1.36      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.16/1.36         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 1.16/1.36          | ~ (r1_xboole_0 @ X1 @ X4))),
% 1.16/1.36      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.16/1.36  thf('11', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i]:
% 1.16/1.36         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.16/1.36      inference('sup-', [status(thm)], ['9', '10'])).
% 1.16/1.36  thf('12', plain,
% 1.16/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.36      inference('sup-', [status(thm)], ['8', '11'])).
% 1.16/1.36  thf('13', plain,
% 1.16/1.36      (![X6 : $i, X7 : $i]:
% 1.16/1.36         ((k4_xboole_0 @ X6 @ X7)
% 1.16/1.36           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.16/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.16/1.36  thf('14', plain,
% 1.16/1.36      (![X0 : $i]:
% 1.16/1.36         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['12', '13'])).
% 1.16/1.36  thf(t5_boole, axiom,
% 1.16/1.36    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.16/1.36  thf('15', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.16/1.36      inference('cnf', [status(esa)], [t5_boole])).
% 1.16/1.36  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.16/1.36      inference('demod', [status(thm)], ['14', '15'])).
% 1.16/1.36  thf(t48_xboole_1, axiom,
% 1.16/1.36    (![A:$i,B:$i]:
% 1.16/1.36     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.16/1.36  thf('17', plain,
% 1.16/1.36      (![X10 : $i, X11 : $i]:
% 1.16/1.36         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.16/1.36           = (k3_xboole_0 @ X10 @ X11))),
% 1.16/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.16/1.36  thf('18', plain,
% 1.16/1.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['16', '17'])).
% 1.16/1.36  thf(idempotence_k3_xboole_0, axiom,
% 1.16/1.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.16/1.36  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.16/1.36      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.16/1.36  thf('20', plain,
% 1.16/1.36      (![X6 : $i, X7 : $i]:
% 1.16/1.36         ((k4_xboole_0 @ X6 @ X7)
% 1.16/1.36           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.16/1.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.16/1.36  thf('21', plain,
% 1.16/1.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['19', '20'])).
% 1.16/1.36  thf('22', plain,
% 1.16/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.16/1.36      inference('sup-', [status(thm)], ['8', '11'])).
% 1.16/1.36  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.16/1.36      inference('demod', [status(thm)], ['18', '21', '22'])).
% 1.16/1.36  thf('24', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.16/1.36      inference('cnf', [status(esa)], [t5_boole])).
% 1.16/1.36  thf('25', plain,
% 1.16/1.36      (((k2_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 1.16/1.36         = (k2_tarski @ sk_B_1 @ sk_C_1))),
% 1.16/1.36      inference('demod', [status(thm)], ['7', '23', '24'])).
% 1.16/1.36  thf(t71_enumset1, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i]:
% 1.16/1.36     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.16/1.36  thf('26', plain,
% 1.16/1.36      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.16/1.36         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 1.16/1.36           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 1.16/1.36      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.16/1.36  thf(t70_enumset1, axiom,
% 1.16/1.36    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.16/1.36  thf('27', plain,
% 1.16/1.36      (![X38 : $i, X39 : $i]:
% 1.16/1.36         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 1.16/1.36      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.16/1.36  thf('28', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i]:
% 1.16/1.36         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['26', '27'])).
% 1.16/1.36  thf(t72_enumset1, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.16/1.36     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.16/1.36  thf('29', plain,
% 1.16/1.36      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.16/1.36         ((k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46)
% 1.16/1.36           = (k2_enumset1 @ X43 @ X44 @ X45 @ X46))),
% 1.16/1.36      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.16/1.36  thf(t55_enumset1, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.16/1.36     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 1.16/1.36       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 1.16/1.36  thf('30', plain,
% 1.16/1.36      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.16/1.36         ((k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 1.16/1.36           = (k2_xboole_0 @ (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35) @ 
% 1.16/1.36              (k1_tarski @ X36)))),
% 1.16/1.36      inference('cnf', [status(esa)], [t55_enumset1])).
% 1.16/1.36  thf('31', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.16/1.36         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.16/1.36           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.16/1.36              (k1_tarski @ X4)))),
% 1.16/1.36      inference('sup+', [status(thm)], ['29', '30'])).
% 1.16/1.36  thf('32', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.36         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 1.16/1.36           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.16/1.36      inference('sup+', [status(thm)], ['28', '31'])).
% 1.16/1.36  thf(t73_enumset1, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.16/1.36     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.16/1.36       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.16/1.36  thf('33', plain,
% 1.16/1.36      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.16/1.36         ((k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51)
% 1.16/1.36           = (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 1.16/1.36      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.16/1.36  thf('34', plain,
% 1.16/1.36      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.16/1.36         ((k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46)
% 1.16/1.36           = (k2_enumset1 @ X43 @ X44 @ X45 @ X46))),
% 1.16/1.36      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.16/1.36  thf('35', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.16/1.36         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.16/1.36           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['33', '34'])).
% 1.16/1.36  thf('36', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.36         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.16/1.36           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.16/1.36      inference('demod', [status(thm)], ['32', '35'])).
% 1.16/1.36  thf('37', plain,
% 1.16/1.36      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.16/1.36         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 1.16/1.36           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 1.16/1.36      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.16/1.36  thf(t102_enumset1, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i]:
% 1.16/1.36     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 1.16/1.36  thf('38', plain,
% 1.16/1.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.16/1.36         ((k1_enumset1 @ X30 @ X29 @ X28) = (k1_enumset1 @ X28 @ X29 @ X30))),
% 1.16/1.36      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.16/1.36  thf('39', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.36         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['37', '38'])).
% 1.16/1.36  thf('40', plain,
% 1.16/1.36      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.16/1.36         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 1.16/1.36           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 1.16/1.36      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.16/1.36  thf('41', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.36         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['39', '40'])).
% 1.16/1.36  thf('42', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.36         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.16/1.36      inference('sup+', [status(thm)], ['37', '38'])).
% 1.16/1.36  thf('43', plain,
% 1.16/1.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.16/1.36         ((k1_enumset1 @ X30 @ X29 @ X28) = (k1_enumset1 @ X28 @ X29 @ X30))),
% 1.16/1.36      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.16/1.36  thf('44', plain,
% 1.16/1.36      (((k1_enumset1 @ sk_A @ sk_C_1 @ sk_B_1) = (k2_tarski @ sk_B_1 @ sk_C_1))),
% 1.16/1.36      inference('demod', [status(thm)], ['25', '36', '41', '42', '43'])).
% 1.16/1.36  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.16/1.36  thf(zf_stmt_3, axiom,
% 1.16/1.36    (![A:$i,B:$i,C:$i,D:$i]:
% 1.16/1.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.16/1.36       ( ![E:$i]:
% 1.16/1.36         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.16/1.36  thf('45', plain,
% 1.16/1.36      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.16/1.36         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.16/1.36          | (r2_hidden @ X21 @ X25)
% 1.16/1.36          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.16/1.36  thf('46', plain,
% 1.16/1.36      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.16/1.36         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 1.16/1.36          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 1.16/1.36      inference('simplify', [status(thm)], ['45'])).
% 1.16/1.36  thf('47', plain,
% 1.16/1.36      (![X0 : $i]:
% 1.16/1.36         ((r2_hidden @ X0 @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 1.16/1.36          | (zip_tseitin_0 @ X0 @ sk_B_1 @ sk_C_1 @ sk_A))),
% 1.16/1.36      inference('sup+', [status(thm)], ['44', '46'])).
% 1.16/1.36  thf('48', plain,
% 1.16/1.36      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.16/1.36         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.36  thf('49', plain,
% 1.16/1.36      (![X16 : $i, X18 : $i, X19 : $i]:
% 1.16/1.36         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 1.16/1.36      inference('simplify', [status(thm)], ['48'])).
% 1.16/1.36  thf('50', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))),
% 1.16/1.36      inference('sup-', [status(thm)], ['47', '49'])).
% 1.16/1.36  thf('51', plain,
% 1.16/1.36      (![X38 : $i, X39 : $i]:
% 1.16/1.36         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 1.16/1.36      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.16/1.36  thf('52', plain,
% 1.16/1.36      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.16/1.36         (~ (r2_hidden @ X26 @ X25)
% 1.16/1.36          | ~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 1.16/1.36          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.16/1.36  thf('53', plain,
% 1.16/1.36      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 1.16/1.36         (~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 1.16/1.36          | ~ (r2_hidden @ X26 @ (k1_enumset1 @ X24 @ X23 @ X22)))),
% 1.16/1.36      inference('simplify', [status(thm)], ['52'])).
% 1.16/1.36  thf('54', plain,
% 1.16/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.36         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.16/1.36          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.16/1.36      inference('sup-', [status(thm)], ['51', '53'])).
% 1.16/1.36  thf('55', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B_1 @ sk_B_1)),
% 1.16/1.36      inference('sup-', [status(thm)], ['50', '54'])).
% 1.16/1.36  thf('56', plain,
% 1.16/1.36      ((((sk_A) = (sk_B_1)) | ((sk_A) = (sk_B_1)) | ((sk_A) = (sk_C_1)))),
% 1.16/1.36      inference('sup-', [status(thm)], ['0', '55'])).
% 1.16/1.36  thf('57', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_B_1)))),
% 1.16/1.36      inference('simplify', [status(thm)], ['56'])).
% 1.16/1.36  thf('58', plain, (((sk_A) != (sk_B_1))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.36  thf('59', plain, (((sk_A) != (sk_C_1))),
% 1.16/1.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.16/1.36  thf('60', plain, ($false),
% 1.16/1.36      inference('simplify_reflect-', [status(thm)], ['57', '58', '59'])).
% 1.16/1.36  
% 1.16/1.36  % SZS output end Refutation
% 1.16/1.36  
% 1.16/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
