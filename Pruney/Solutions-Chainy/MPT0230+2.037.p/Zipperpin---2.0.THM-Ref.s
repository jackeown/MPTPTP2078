%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J8YcM45ajb

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:15 EST 2020

% Result     : Theorem 4.81s
% Output     : Refutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 140 expanded)
%              Number of leaves         :   40 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  898 (1144 expanded)
%              Number of equality atoms :   96 ( 126 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 ) ) ),
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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('32',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k5_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      = ( k4_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('39',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_enumset1 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_enumset1 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X29 @ X28 @ X27 )
      = ( k1_enumset1 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('49',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X65 @ X67 @ X66 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('50',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X29 @ X28 @ X27 )
      = ( k1_enumset1 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('55',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X65 @ X67 @ X66 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('56',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['28','43','48','53','54','55'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('65',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','67'])).

thf('69',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','70','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J8YcM45ajb
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:34:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 4.81/4.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.81/4.99  % Solved by: fo/fo7.sh
% 4.81/4.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.81/4.99  % done 5174 iterations in 4.546s
% 4.81/4.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.81/4.99  % SZS output start Refutation
% 4.81/4.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.81/4.99  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.81/4.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.81/4.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 4.81/4.99  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 4.81/4.99  thf(sk_C_type, type, sk_C: $i).
% 4.81/4.99  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.81/4.99  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.81/4.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.81/4.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.81/4.99  thf(sk_B_type, type, sk_B: $i).
% 4.81/4.99  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.81/4.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.81/4.99  thf(sk_A_type, type, sk_A: $i).
% 4.81/4.99  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.81/4.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.81/4.99  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 4.81/4.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.81/4.99  thf(d1_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i,D:$i]:
% 4.81/4.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.81/4.99       ( ![E:$i]:
% 4.81/4.99         ( ( r2_hidden @ E @ D ) <=>
% 4.81/4.99           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 4.81/4.99  thf(zf_stmt_0, axiom,
% 4.81/4.99    (![E:$i,C:$i,B:$i,A:$i]:
% 4.81/4.99     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 4.81/4.99       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 4.81/4.99  thf('0', plain,
% 4.81/4.99      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 4.81/4.99         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 4.81/4.99          | ((X16) = (X17))
% 4.81/4.99          | ((X16) = (X18))
% 4.81/4.99          | ((X16) = (X19)))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf(t25_zfmisc_1, conjecture,
% 4.81/4.99    (![A:$i,B:$i,C:$i]:
% 4.81/4.99     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 4.81/4.99          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 4.81/4.99  thf(zf_stmt_1, negated_conjecture,
% 4.81/4.99    (~( ![A:$i,B:$i,C:$i]:
% 4.81/4.99        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 4.81/4.99             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 4.81/4.99    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 4.81/4.99  thf('1', plain,
% 4.81/4.99      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.81/4.99  thf(t28_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.81/4.99  thf('2', plain,
% 4.81/4.99      (![X7 : $i, X8 : $i]:
% 4.81/4.99         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 4.81/4.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.81/4.99  thf('3', plain,
% 4.81/4.99      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 4.81/4.99         = (k1_tarski @ sk_A))),
% 4.81/4.99      inference('sup-', [status(thm)], ['1', '2'])).
% 4.81/4.99  thf(t100_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.81/4.99  thf('4', plain,
% 4.81/4.99      (![X3 : $i, X4 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X3 @ X4)
% 4.81/4.99           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.81/4.99  thf('5', plain,
% 4.81/4.99      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 4.81/4.99         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['3', '4'])).
% 4.81/4.99  thf(t17_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.81/4.99  thf('6', plain,
% 4.81/4.99      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 4.81/4.99      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.81/4.99  thf(t3_xboole_1, axiom,
% 4.81/4.99    (![A:$i]:
% 4.81/4.99     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.81/4.99  thf('7', plain,
% 4.81/4.99      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 4.81/4.99      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.81/4.99  thf('8', plain,
% 4.81/4.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.81/4.99      inference('sup-', [status(thm)], ['6', '7'])).
% 4.81/4.99  thf(commutativity_k3_xboole_0, axiom,
% 4.81/4.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.81/4.99  thf('9', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.81/4.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.81/4.99  thf('10', plain,
% 4.81/4.99      (![X3 : $i, X4 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X3 @ X4)
% 4.81/4.99           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.81/4.99  thf('11', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X0 @ X1)
% 4.81/4.99           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['9', '10'])).
% 4.81/4.99  thf('12', plain,
% 4.81/4.99      (![X0 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['8', '11'])).
% 4.81/4.99  thf(t5_boole, axiom,
% 4.81/4.99    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.81/4.99  thf('13', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 4.81/4.99      inference('cnf', [status(esa)], [t5_boole])).
% 4.81/4.99  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.81/4.99      inference('demod', [status(thm)], ['12', '13'])).
% 4.81/4.99  thf(t48_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.81/4.99  thf('15', plain,
% 4.81/4.99      (![X10 : $i, X11 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 4.81/4.99           = (k3_xboole_0 @ X10 @ X11))),
% 4.81/4.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.81/4.99  thf('16', plain,
% 4.81/4.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['14', '15'])).
% 4.81/4.99  thf(idempotence_k3_xboole_0, axiom,
% 4.81/4.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 4.81/4.99  thf('17', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 4.81/4.99      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 4.81/4.99  thf('18', plain,
% 4.81/4.99      (![X3 : $i, X4 : $i]:
% 4.81/4.99         ((k4_xboole_0 @ X3 @ X4)
% 4.81/4.99           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.81/4.99  thf('19', plain,
% 4.81/4.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['17', '18'])).
% 4.81/4.99  thf('20', plain,
% 4.81/4.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.81/4.99      inference('sup-', [status(thm)], ['6', '7'])).
% 4.81/4.99  thf('21', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.81/4.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.81/4.99  thf('22', plain,
% 4.81/4.99      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['20', '21'])).
% 4.81/4.99  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.81/4.99      inference('demod', [status(thm)], ['16', '19', '22'])).
% 4.81/4.99  thf('24', plain,
% 4.81/4.99      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 4.81/4.99         = (k1_xboole_0))),
% 4.81/4.99      inference('demod', [status(thm)], ['5', '23'])).
% 4.81/4.99  thf(t98_xboole_1, axiom,
% 4.81/4.99    (![A:$i,B:$i]:
% 4.81/4.99     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 4.81/4.99  thf('25', plain,
% 4.81/4.99      (![X13 : $i, X14 : $i]:
% 4.81/4.99         ((k2_xboole_0 @ X13 @ X14)
% 4.81/4.99           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 4.81/4.99  thf('26', plain,
% 4.81/4.99      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 4.81/4.99         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['24', '25'])).
% 4.81/4.99  thf('27', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 4.81/4.99      inference('cnf', [status(esa)], [t5_boole])).
% 4.81/4.99  thf('28', plain,
% 4.81/4.99      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 4.81/4.99         = (k2_tarski @ sk_B @ sk_C))),
% 4.81/4.99      inference('demod', [status(thm)], ['26', '27'])).
% 4.81/4.99  thf(t71_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i]:
% 4.81/4.99     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.81/4.99  thf('29', plain,
% 4.81/4.99      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 4.81/4.99           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 4.81/4.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.81/4.99  thf(t70_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.81/4.99  thf('30', plain,
% 4.81/4.99      (![X38 : $i, X39 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 4.81/4.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.81/4.99  thf('31', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['29', '30'])).
% 4.81/4.99  thf(t74_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.81/4.99     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 4.81/4.99       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 4.81/4.99  thf('32', plain,
% 4.81/4.99      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 4.81/4.99         ((k5_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 4.81/4.99           = (k4_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57))),
% 4.81/4.99      inference('cnf', [status(esa)], [t74_enumset1])).
% 4.81/4.99  thf(t73_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.81/4.99     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 4.81/4.99       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 4.81/4.99  thf('33', plain,
% 4.81/4.99      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 4.81/4.99         ((k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51)
% 4.81/4.99           = (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 4.81/4.99      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.81/4.99  thf('34', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.81/4.99         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 4.81/4.99           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['32', '33'])).
% 4.81/4.99  thf('35', plain,
% 4.81/4.99      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 4.81/4.99         ((k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51)
% 4.81/4.99           = (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 4.81/4.99      inference('cnf', [status(esa)], [t73_enumset1])).
% 4.81/4.99  thf(t61_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 4.81/4.99     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 4.81/4.99       ( k2_xboole_0 @
% 4.81/4.99         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 4.81/4.99  thf('36', plain,
% 4.81/4.99      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.81/4.99         ((k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 4.81/4.99           = (k2_xboole_0 @ 
% 4.81/4.99              (k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35) @ 
% 4.81/4.99              (k1_tarski @ X36)))),
% 4.81/4.99      inference('cnf', [status(esa)], [t61_enumset1])).
% 4.81/4.99  thf('37', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.81/4.99         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 4.81/4.99           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 4.81/4.99              (k1_tarski @ X5)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['35', '36'])).
% 4.81/4.99  thf('38', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.81/4.99         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 4.81/4.99           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 4.81/4.99              (k1_tarski @ X0)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['34', '37'])).
% 4.81/4.99  thf(t72_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i,D:$i]:
% 4.81/4.99     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.81/4.99  thf('39', plain,
% 4.81/4.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.81/4.99         ((k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46)
% 4.81/4.99           = (k2_enumset1 @ X43 @ X44 @ X45 @ X46))),
% 4.81/4.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.81/4.99  thf('40', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.81/4.99         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 4.81/4.99           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 4.81/4.99              (k1_tarski @ X0)))),
% 4.81/4.99      inference('demod', [status(thm)], ['38', '39'])).
% 4.81/4.99  thf('41', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 4.81/4.99           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 4.81/4.99      inference('sup+', [status(thm)], ['31', '40'])).
% 4.81/4.99  thf('42', plain,
% 4.81/4.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 4.81/4.99         ((k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46)
% 4.81/4.99           = (k2_enumset1 @ X43 @ X44 @ X45 @ X46))),
% 4.81/4.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.81/4.99  thf('43', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 4.81/4.99           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 4.81/4.99      inference('demod', [status(thm)], ['41', '42'])).
% 4.81/4.99  thf('44', plain,
% 4.81/4.99      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 4.81/4.99           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 4.81/4.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.81/4.99  thf(t102_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i]:
% 4.81/4.99     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 4.81/4.99  thf('45', plain,
% 4.81/4.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X29 @ X28 @ X27) = (k1_enumset1 @ X27 @ X28 @ X29))),
% 4.81/4.99      inference('cnf', [status(esa)], [t102_enumset1])).
% 4.81/4.99  thf('46', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['44', '45'])).
% 4.81/4.99  thf('47', plain,
% 4.81/4.99      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 4.81/4.99           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 4.81/4.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.81/4.99  thf('48', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X0 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['46', '47'])).
% 4.81/4.99  thf(t98_enumset1, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i]:
% 4.81/4.99     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 4.81/4.99  thf('49', plain,
% 4.81/4.99      (![X65 : $i, X66 : $i, X67 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X65 @ X67 @ X66) = (k1_enumset1 @ X65 @ X66 @ X67))),
% 4.81/4.99      inference('cnf', [status(esa)], [t98_enumset1])).
% 4.81/4.99  thf('50', plain,
% 4.81/4.99      (![X27 : $i, X28 : $i, X29 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X29 @ X28 @ X27) = (k1_enumset1 @ X27 @ X28 @ X29))),
% 4.81/4.99      inference('cnf', [status(esa)], [t102_enumset1])).
% 4.81/4.99  thf('51', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['49', '50'])).
% 4.81/4.99  thf('52', plain,
% 4.81/4.99      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 4.81/4.99           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 4.81/4.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.81/4.99  thf('53', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['51', '52'])).
% 4.81/4.99  thf('54', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.81/4.99      inference('sup+', [status(thm)], ['49', '50'])).
% 4.81/4.99  thf('55', plain,
% 4.81/4.99      (![X65 : $i, X66 : $i, X67 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X65 @ X67 @ X66) = (k1_enumset1 @ X65 @ X66 @ X67))),
% 4.81/4.99      inference('cnf', [status(esa)], [t98_enumset1])).
% 4.81/4.99  thf('56', plain,
% 4.81/4.99      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 4.81/4.99      inference('demod', [status(thm)], ['28', '43', '48', '53', '54', '55'])).
% 4.81/4.99  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 4.81/4.99  thf(zf_stmt_3, axiom,
% 4.81/4.99    (![A:$i,B:$i,C:$i,D:$i]:
% 4.81/4.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.81/4.99       ( ![E:$i]:
% 4.81/4.99         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 4.81/4.99  thf('57', plain,
% 4.81/4.99      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 4.81/4.99         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 4.81/4.99          | (r2_hidden @ X20 @ X24)
% 4.81/4.99          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.81/4.99  thf('58', plain,
% 4.81/4.99      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 4.81/4.99         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 4.81/4.99          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 4.81/4.99      inference('simplify', [status(thm)], ['57'])).
% 4.81/4.99  thf('59', plain,
% 4.81/4.99      (![X0 : $i]:
% 4.81/4.99         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 4.81/4.99          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 4.81/4.99      inference('sup+', [status(thm)], ['56', '58'])).
% 4.81/4.99  thf('60', plain,
% 4.81/4.99      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 4.81/4.99         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.81/4.99  thf('61', plain,
% 4.81/4.99      (![X15 : $i, X17 : $i, X18 : $i]:
% 4.81/4.99         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 4.81/4.99      inference('simplify', [status(thm)], ['60'])).
% 4.81/4.99  thf('62', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 4.81/4.99      inference('sup-', [status(thm)], ['59', '61'])).
% 4.81/4.99  thf('63', plain,
% 4.81/4.99      (![X38 : $i, X39 : $i]:
% 4.81/4.99         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 4.81/4.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.81/4.99  thf('64', plain,
% 4.81/4.99      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 4.81/4.99         (~ (r2_hidden @ X25 @ X24)
% 4.81/4.99          | ~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 4.81/4.99          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.81/4.99  thf('65', plain,
% 4.81/4.99      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 4.81/4.99         (~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 4.81/4.99          | ~ (r2_hidden @ X25 @ (k1_enumset1 @ X23 @ X22 @ X21)))),
% 4.81/4.99      inference('simplify', [status(thm)], ['64'])).
% 4.81/4.99  thf('66', plain,
% 4.81/4.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.81/4.99         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.81/4.99          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 4.81/4.99      inference('sup-', [status(thm)], ['63', '65'])).
% 4.81/4.99  thf('67', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 4.81/4.99      inference('sup-', [status(thm)], ['62', '66'])).
% 4.81/4.99  thf('68', plain,
% 4.81/4.99      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 4.81/4.99      inference('sup-', [status(thm)], ['0', '67'])).
% 4.81/4.99  thf('69', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 4.81/4.99      inference('simplify', [status(thm)], ['68'])).
% 4.81/4.99  thf('70', plain, (((sk_A) != (sk_B))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.81/4.99  thf('71', plain, (((sk_A) != (sk_C))),
% 4.81/4.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.81/4.99  thf('72', plain, ($false),
% 4.81/4.99      inference('simplify_reflect-', [status(thm)], ['69', '70', '71'])).
% 4.81/4.99  
% 4.81/4.99  % SZS output end Refutation
% 4.81/4.99  
% 4.81/5.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
