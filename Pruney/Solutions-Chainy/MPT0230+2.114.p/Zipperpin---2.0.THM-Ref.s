%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HJVsUOAk70

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:23 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 170 expanded)
%              Number of leaves         :   40 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  806 (1304 expanded)
%              Number of equality atoms :   81 ( 144 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','12'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('35',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('36',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('42',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('48',plain,
    ( ( k1_enumset1 @ sk_B_1 @ sk_C_1 @ sk_A )
    = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','46','47'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X18 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,
    ( ( sk_A = sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','59'])).

thf('61',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_B_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','62','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HJVsUOAk70
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:07:33 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 537 iterations in 0.154s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.61  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.43/0.61  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.43/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.43/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(d1_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.61       ( ![E:$i]:
% 0.43/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.43/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, axiom,
% 0.43/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.43/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.43/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.61         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.43/0.61          | ((X17) = (X18))
% 0.43/0.61          | ((X17) = (X19))
% 0.43/0.61          | ((X17) = (X20)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t25_zfmisc_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.43/0.61          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_1, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.43/0.61             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.61  thf(t28_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X8 : $i, X9 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.43/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.43/0.61         = (k1_tarski @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.61  thf(t100_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X6 @ X7)
% 0.43/0.61           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.43/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.61  thf(t3_boole, axiom,
% 0.43/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.43/0.61  thf('6', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.61  thf(t48_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.43/0.61           = (k3_xboole_0 @ X11 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['6', '7'])).
% 0.43/0.61  thf(idempotence_k3_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.61  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X6 @ X7)
% 0.43/0.61           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['8', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.43/0.61         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['5', '12'])).
% 0.43/0.61  thf(t7_xboole_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['8', '11'])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['8', '11'])).
% 0.43/0.61  thf(t4_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.43/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.43/0.61          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.43/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.43/0.61          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.43/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.43/0.61  thf('19', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.43/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['15', '20'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.43/0.61         = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['13', '22'])).
% 0.43/0.61  thf(t98_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         ((k2_xboole_0 @ X14 @ X15)
% 0.43/0.61           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.43/0.61         = (k5_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['23', '24'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '21'])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X6 @ X7)
% 0.43/0.61           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf('29', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.43/0.61  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.43/0.61         = (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['25', '30'])).
% 0.43/0.61  thf(t71_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 0.43/0.61           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.43/0.61  thf(t70_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X36 : $i, X37 : $i]:
% 0.43/0.61         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.43/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf(t74_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.61     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.43/0.61       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.43/0.61         ((k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 0.43/0.61           = (k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 0.43/0.61      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.43/0.61  thf(t73_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.43/0.61     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.43/0.61       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.43/0.61         ((k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.43/0.61           = (k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.43/0.61      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.61           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['35', '36'])).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.43/0.61         ((k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.43/0.61           = (k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.43/0.61      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.43/0.61  thf(t61_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.43/0.61     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.43/0.61       ( k2_xboole_0 @
% 0.43/0.61         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.43/0.61         ((k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.43/0.61           = (k2_xboole_0 @ 
% 0.43/0.61              (k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33) @ 
% 0.43/0.61              (k1_tarski @ X34)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.61         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.43/0.61           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.43/0.61              (k1_tarski @ X5)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.61           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.43/0.61              (k1_tarski @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['37', '40'])).
% 0.43/0.61  thf(t72_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.43/0.61         ((k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44)
% 0.43/0.61           = (k2_enumset1 @ X41 @ X42 @ X43 @ X44))),
% 0.43/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.43/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.43/0.62              (k1_tarski @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.43/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['34', '43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.43/0.62         ((k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44)
% 0.43/0.62           = (k2_enumset1 @ X41 @ X42 @ X43 @ X44))),
% 0.43/0.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.43/0.62           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.43/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.43/0.62         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 0.43/0.62           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 0.43/0.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      (((k1_enumset1 @ sk_B_1 @ sk_C_1 @ sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['31', '46', '47'])).
% 0.43/0.62  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_3, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.62       ( ![E:$i]:
% 0.43/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.43/0.62          | (r2_hidden @ X21 @ X25)
% 0.43/0.62          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.62         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 0.43/0.62          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 0.43/0.62      inference('simplify', [status(thm)], ['49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ X0 @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.43/0.62          | (zip_tseitin_0 @ X0 @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.43/0.62      inference('sup+', [status(thm)], ['48', '50'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.43/0.62         (((X17) != (X18)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.43/0.62         ~ (zip_tseitin_0 @ X18 @ X18 @ X19 @ X16)),
% 0.43/0.62      inference('simplify', [status(thm)], ['52'])).
% 0.43/0.62  thf('54', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['51', '53'])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (![X36 : $i, X37 : $i]:
% 0.43/0.62         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.43/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X26 @ X25)
% 0.43/0.62          | ~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.43/0.62          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 0.43/0.62         (~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.43/0.62          | ~ (r2_hidden @ X26 @ (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['56'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.43/0.62          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['55', '57'])).
% 0.43/0.62  thf('59', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B_1 @ sk_B_1)),
% 0.43/0.62      inference('sup-', [status(thm)], ['54', '58'])).
% 0.43/0.62  thf('60', plain,
% 0.43/0.62      ((((sk_A) = (sk_B_1)) | ((sk_A) = (sk_B_1)) | ((sk_A) = (sk_C_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '59'])).
% 0.43/0.62  thf('61', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_B_1)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.43/0.62  thf('62', plain, (((sk_A) != (sk_B_1))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('63', plain, (((sk_A) != (sk_C_1))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.62  thf('64', plain, ($false),
% 0.43/0.62      inference('simplify_reflect-', [status(thm)], ['61', '62', '63'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
