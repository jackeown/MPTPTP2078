%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYncStcvR2

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:45 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 143 expanded)
%              Number of leaves         :   39 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  731 (1037 expanded)
%              Number of equality atoms :   80 ( 103 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','35'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','41','42'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('44',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('46',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X40 @ X41 @ X42 ) @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('49',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( k2_enumset1 @ X47 @ X47 @ X48 @ X49 )
      = ( k1_enumset1 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('50',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( k2_tarski @ sk_B_1 @ sk_A )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
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

thf('55',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X25 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('62',plain,(
    ! [X35: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ( X38 = X35 )
      | ( X37
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('63',plain,(
    ! [X35: $i,X38: $i] :
      ( ( X38 = X35 )
      | ~ ( r2_hidden @ X38 @ ( k1_tarski @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_A = sk_B_1 ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYncStcvR2
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 1029 iterations in 0.448s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.71/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.71/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.71/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.71/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.71/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.90  thf(t6_zfmisc_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.71/0.90       ( ( A ) = ( B ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i]:
% 0.71/0.90        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.71/0.90          ( ( A ) = ( B ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.71/0.90  thf('0', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t28_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.71/0.90         = (k1_tarski @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['0', '1'])).
% 0.71/0.90  thf(t100_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X9 @ X10)
% 0.71/0.90           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.71/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['2', '3'])).
% 0.71/0.90  thf(idempotence_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.71/0.90  thf('5', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.71/0.90      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X9 @ X10)
% 0.71/0.90           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.71/0.90         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['4', '7'])).
% 0.71/0.90  thf(t98_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (![X21 : $i, X22 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X21 @ X22)
% 0.71/0.90           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.71/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_B_1) @ 
% 0.71/0.90            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['8', '9'])).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.71/0.90  thf(t91_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.71/0.90       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.71/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.71/0.90           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.71/0.90           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['12', '13'])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.71/0.90           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['11', '14'])).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X21 : $i, X22 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X21 @ X22)
% 0.71/0.90           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.71/0.90  thf(idempotence_k2_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.71/0.90  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.71/0.90      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.71/0.90  thf(t79_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.71/0.90  thf('19', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.71/0.90      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.71/0.90  thf(t4_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.71/0.90            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      (![X4 : $i, X5 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X4 @ X5)
% 0.71/0.90          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.71/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.71/0.90          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.71/0.90          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['21', '22'])).
% 0.71/0.90  thf('24', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['20', '23'])).
% 0.71/0.90  thf('25', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['19', '24'])).
% 0.71/0.90  thf(t7_xboole_0, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.71/0.90          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.71/0.90  thf('26', plain,
% 0.71/0.90      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.71/0.90      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.71/0.90  thf('27', plain,
% 0.71/0.90      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.71/0.90          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.71/0.90  thf('28', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['25', '28'])).
% 0.71/0.90  thf('30', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X9 @ X10)
% 0.71/0.90           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['29', '30'])).
% 0.71/0.90  thf(t5_boole, axiom,
% 0.71/0.90    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.71/0.90  thf('32', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t5_boole])).
% 0.71/0.90  thf('33', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['31', '32'])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      (![X21 : $i, X22 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X21 @ X22)
% 0.71/0.90           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.71/0.90           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['33', '34'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['18', '35'])).
% 0.71/0.90  thf(t21_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      (![X11 : $i, X12 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 0.71/0.90      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.71/0.90           = (k4_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['36', '37'])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('40', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['25', '28'])).
% 0.71/0.90  thf('41', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.71/0.90  thf('42', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t5_boole])).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      (((k2_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.71/0.90         = (k1_tarski @ sk_B_1))),
% 0.71/0.90      inference('demod', [status(thm)], ['10', '41', '42'])).
% 0.71/0.90  thf(t69_enumset1, axiom,
% 0.71/0.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.71/0.90  thf('44', plain,
% 0.71/0.90      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.71/0.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.71/0.90  thf(t70_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      (![X45 : $i, X46 : $i]:
% 0.71/0.90         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.71/0.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.71/0.90  thf(t46_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.71/0.90       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X40 @ X41 @ X42 @ X43)
% 0.71/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X40 @ X41 @ X42) @ (k1_tarski @ X43)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.71/0.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['45', '46'])).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.71/0.90           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['44', '47'])).
% 0.71/0.90  thf(t71_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.71/0.90  thf('49', plain,
% 0.71/0.90      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X47 @ X47 @ X48 @ X49)
% 0.71/0.90           = (k1_enumset1 @ X47 @ X48 @ X49))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (![X45 : $i, X46 : $i]:
% 0.71/0.90         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.71/0.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.71/0.90  thf('51', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['49', '50'])).
% 0.71/0.90  thf('52', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_tarski @ X0 @ X1)
% 0.71/0.90           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['48', '51'])).
% 0.71/0.90  thf('53', plain, (((k2_tarski @ sk_B_1 @ sk_A) = (k1_tarski @ sk_B_1))),
% 0.71/0.90      inference('demod', [status(thm)], ['43', '52'])).
% 0.71/0.90  thf('54', plain,
% 0.71/0.90      (![X45 : $i, X46 : $i]:
% 0.71/0.90         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 0.71/0.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.71/0.90  thf(d1_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.71/0.90       ( ![E:$i]:
% 0.71/0.90         ( ( r2_hidden @ E @ D ) <=>
% 0.71/0.90           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.71/0.90  thf(zf_stmt_2, axiom,
% 0.71/0.90    (![E:$i,C:$i,B:$i,A:$i]:
% 0.71/0.90     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.71/0.90       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_3, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.71/0.90       ( ![E:$i]:
% 0.71/0.90         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.71/0.90          | (r2_hidden @ X28 @ X32)
% 0.71/0.90          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.90  thf('56', plain,
% 0.71/0.90      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.71/0.90         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 0.71/0.90          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 0.71/0.90      inference('simplify', [status(thm)], ['55'])).
% 0.71/0.90  thf('57', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.71/0.90          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['54', '56'])).
% 0.71/0.90  thf('58', plain,
% 0.71/0.90      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.71/0.90         (((X24) != (X25)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.71/0.90  thf('59', plain,
% 0.71/0.90      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.71/0.90         ~ (zip_tseitin_0 @ X25 @ X25 @ X26 @ X23)),
% 0.71/0.90      inference('simplify', [status(thm)], ['58'])).
% 0.71/0.90  thf('60', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['57', '59'])).
% 0.71/0.90  thf('61', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['53', '60'])).
% 0.71/0.90  thf(d1_tarski, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.71/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.71/0.90  thf('62', plain,
% 0.71/0.90      (![X35 : $i, X37 : $i, X38 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X38 @ X37)
% 0.71/0.90          | ((X38) = (X35))
% 0.71/0.90          | ((X37) != (k1_tarski @ X35)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d1_tarski])).
% 0.71/0.90  thf('63', plain,
% 0.71/0.90      (![X35 : $i, X38 : $i]:
% 0.71/0.90         (((X38) = (X35)) | ~ (r2_hidden @ X38 @ (k1_tarski @ X35)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['62'])).
% 0.71/0.90  thf('64', plain, (((sk_A) = (sk_B_1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['61', '63'])).
% 0.71/0.90  thf('65', plain, (((sk_A) != (sk_B_1))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('66', plain, ($false),
% 0.71/0.90      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
