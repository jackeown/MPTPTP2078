%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCUH54SFOA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:38 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 906 expanded)
%              Number of leaves         :   38 ( 318 expanded)
%              Depth                    :   25
%              Number of atoms          : 1330 (7477 expanded)
%              Number of equality atoms :  139 ( 809 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X68: $i,X69: $i] :
      ( r1_tarski @ ( k1_tarski @ X68 ) @ ( k2_tarski @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','31'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('39',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_enumset1 @ sk_A @ sk_C @ sk_C @ sk_D )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['37','40'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('42',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('43',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('46',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('49',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X68: $i,X69: $i] :
      ( r1_tarski @ ( k1_tarski @ X68 ) @ ( k2_tarski @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('58',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('60',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27','30'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ sk_B ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['60','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('78',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('79',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_B )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('85',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_C @ sk_D @ X0 )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('88',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_C @ sk_D @ sk_B @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ sk_C @ sk_D @ sk_C ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_B )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('92',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_C @ sk_D @ sk_B @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('95',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_C @ sk_D @ sk_B @ X0 )
      = ( k1_enumset1 @ sk_C @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_C @ sk_D @ X0 )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','96','97'])).

thf('99',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('100',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_C )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ sk_C @ sk_D @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_C @ sk_D @ X0 )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','96','97'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_C @ sk_D @ X0 )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('105',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('106',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_C )
    = ( k1_enumset1 @ sk_C @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_B )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('108',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_C )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_C @ sk_D @ X0 )
      = ( k2_enumset1 @ X0 @ sk_C @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['102','103','108','109'])).

thf('111',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_A )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['41','110'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('112',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('113',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C ) ) ),
    inference('sup+',[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X22 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('119',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('120',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','120'])).

thf('122',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['117','121'])).

thf('123',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['0','122'])).

thf('124',plain,
    ( ( sk_A = sk_D )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('126',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','125','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCUH54SFOA
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.87/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.87/1.03  % Solved by: fo/fo7.sh
% 0.87/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.03  % done 1486 iterations in 0.607s
% 0.87/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.87/1.03  % SZS output start Refutation
% 0.87/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.87/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.87/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.87/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.87/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.87/1.03  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.87/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.87/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.87/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.87/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.87/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.87/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.87/1.03  thf(d1_enumset1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.87/1.03       ( ![E:$i]:
% 0.87/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.87/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.87/1.03  thf(zf_stmt_0, axiom,
% 0.87/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.87/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.87/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.87/1.03  thf('0', plain,
% 0.87/1.03      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.87/1.03         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.87/1.03          | ((X21) = (X22))
% 0.87/1.03          | ((X21) = (X23))
% 0.87/1.03          | ((X21) = (X24)))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.03  thf(t12_zfmisc_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.87/1.03  thf('1', plain,
% 0.87/1.03      (![X68 : $i, X69 : $i]:
% 0.87/1.03         (r1_tarski @ (k1_tarski @ X68) @ (k2_tarski @ X68 @ X69))),
% 0.87/1.03      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.87/1.03  thf(t28_zfmisc_1, conjecture,
% 0.87/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.03     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.87/1.03          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.87/1.03  thf(zf_stmt_1, negated_conjecture,
% 0.87/1.03    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.03        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.87/1.03             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.87/1.03    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.87/1.03  thf('2', plain,
% 0.87/1.03      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.87/1.03  thf(t28_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.87/1.03  thf('3', plain,
% 0.87/1.03      (![X12 : $i, X13 : $i]:
% 0.87/1.03         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.87/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.03  thf('4', plain,
% 0.87/1.03      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.87/1.03         = (k2_tarski @ sk_A @ sk_B))),
% 0.87/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.87/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.87/1.03  thf('5', plain,
% 0.87/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.03  thf(t18_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i]:
% 0.87/1.03     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.87/1.03  thf('6', plain,
% 0.87/1.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.87/1.03         ((r1_tarski @ X9 @ X10)
% 0.87/1.03          | ~ (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.87/1.03  thf('7', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['5', '6'])).
% 0.87/1.03  thf('8', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.87/1.03          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['4', '7'])).
% 0.87/1.03  thf('9', plain,
% 0.87/1.03      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('sup-', [status(thm)], ['1', '8'])).
% 0.87/1.03  thf('10', plain,
% 0.87/1.03      (![X12 : $i, X13 : $i]:
% 0.87/1.03         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.87/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.03  thf('11', plain,
% 0.87/1.03      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.87/1.03         = (k1_tarski @ sk_A))),
% 0.87/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.87/1.03  thf(t100_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.87/1.03  thf('12', plain,
% 0.87/1.03      (![X5 : $i, X6 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X5 @ X6)
% 0.87/1.03           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.03  thf('13', plain,
% 0.87/1.03      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.87/1.03         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['11', '12'])).
% 0.87/1.03  thf(t17_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.87/1.03  thf('14', plain,
% 0.87/1.03      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.87/1.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.87/1.03  thf(t3_xboole_1, axiom,
% 0.87/1.03    (![A:$i]:
% 0.87/1.03     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.87/1.03  thf('15', plain,
% 0.87/1.03      (![X14 : $i]:
% 0.87/1.03         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 0.87/1.03      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.87/1.03  thf('16', plain,
% 0.87/1.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.87/1.03  thf('17', plain,
% 0.87/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.03  thf('18', plain,
% 0.87/1.03      (![X5 : $i, X6 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X5 @ X6)
% 0.87/1.03           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.03  thf('19', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X0 @ X1)
% 0.87/1.03           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['17', '18'])).
% 0.87/1.03  thf('20', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['16', '19'])).
% 0.87/1.03  thf(t5_boole, axiom,
% 0.87/1.03    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.87/1.03  thf('21', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.87/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.87/1.03  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.87/1.03      inference('demod', [status(thm)], ['20', '21'])).
% 0.87/1.03  thf(t48_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.87/1.03  thf('23', plain,
% 0.87/1.03      (![X15 : $i, X16 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.87/1.03           = (k3_xboole_0 @ X15 @ X16))),
% 0.87/1.03      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.87/1.03  thf('24', plain,
% 0.87/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['22', '23'])).
% 0.87/1.03  thf(idempotence_k3_xboole_0, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.87/1.03  thf('25', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.87/1.03      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.87/1.03  thf('26', plain,
% 0.87/1.03      (![X5 : $i, X6 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X5 @ X6)
% 0.87/1.03           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.87/1.03  thf('27', plain,
% 0.87/1.03      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['25', '26'])).
% 0.87/1.03  thf('28', plain,
% 0.87/1.03      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.87/1.03      inference('sup-', [status(thm)], ['14', '15'])).
% 0.87/1.03  thf('29', plain,
% 0.87/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.03  thf('30', plain,
% 0.87/1.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['28', '29'])).
% 0.87/1.03  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.87/1.03      inference('demod', [status(thm)], ['24', '27', '30'])).
% 0.87/1.03  thf('32', plain,
% 0.87/1.03      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.87/1.03         = (k1_xboole_0))),
% 0.87/1.03      inference('demod', [status(thm)], ['13', '31'])).
% 0.87/1.03  thf(t98_xboole_1, axiom,
% 0.87/1.03    (![A:$i,B:$i]:
% 0.87/1.03     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.87/1.03  thf('33', plain,
% 0.87/1.03      (![X18 : $i, X19 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ X18 @ X19)
% 0.87/1.03           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.87/1.03  thf('34', plain,
% 0.87/1.03      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_A))
% 0.87/1.03         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ k1_xboole_0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['32', '33'])).
% 0.87/1.03  thf(commutativity_k2_xboole_0, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.87/1.03  thf('35', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.87/1.03  thf('36', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.87/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.87/1.03  thf('37', plain,
% 0.87/1.03      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))
% 0.87/1.03         = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.87/1.03  thf(t70_enumset1, axiom,
% 0.87/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.87/1.03  thf('38', plain,
% 0.87/1.03      (![X41 : $i, X42 : $i]:
% 0.87/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.87/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.87/1.03  thf(t44_enumset1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.03     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.87/1.03       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.87/1.03  thf('39', plain,
% 0.87/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_enumset1 @ X33 @ X34 @ X35)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.87/1.03  thf('40', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['38', '39'])).
% 0.87/1.03  thf('41', plain,
% 0.87/1.03      (((k2_enumset1 @ sk_A @ sk_C @ sk_C @ sk_D) = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('demod', [status(thm)], ['37', '40'])).
% 0.87/1.03  thf(t71_enumset1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i]:
% 0.87/1.03     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.87/1.03  thf('42', plain,
% 0.87/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.87/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.87/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.87/1.03  thf('43', plain,
% 0.87/1.03      (![X41 : $i, X42 : $i]:
% 0.87/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.87/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.87/1.03  thf('44', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['42', '43'])).
% 0.87/1.03  thf('45', plain,
% 0.87/1.03      (![X41 : $i, X42 : $i]:
% 0.87/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.87/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.87/1.03  thf(t46_enumset1, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.03     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.87/1.03       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.87/1.03  thf('46', plain,
% 0.87/1.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.87/1.03           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.87/1.03  thf('47', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.87/1.03           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['45', '46'])).
% 0.87/1.03  thf('48', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k2_tarski @ X1 @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['44', '47'])).
% 0.87/1.03  thf(t69_enumset1, axiom,
% 0.87/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.87/1.03  thf('49', plain,
% 0.87/1.03      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.87/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.87/1.03  thf('50', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k2_tarski @ X1 @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.87/1.03      inference('demod', [status(thm)], ['48', '49'])).
% 0.87/1.03  thf('51', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.87/1.03  thf('52', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.87/1.03           = (k2_tarski @ X1 @ X0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['50', '51'])).
% 0.87/1.03  thf('53', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k2_tarski @ X1 @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.87/1.03      inference('demod', [status(thm)], ['48', '49'])).
% 0.87/1.03  thf('54', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['52', '53'])).
% 0.87/1.03  thf('55', plain,
% 0.87/1.03      (![X68 : $i, X69 : $i]:
% 0.87/1.03         (r1_tarski @ (k1_tarski @ X68) @ (k2_tarski @ X68 @ X69))),
% 0.87/1.03      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.87/1.03  thf('56', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['54', '55'])).
% 0.87/1.03  thf('57', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.87/1.03          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['4', '7'])).
% 0.87/1.03  thf('58', plain,
% 0.87/1.03      ((r1_tarski @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('sup-', [status(thm)], ['56', '57'])).
% 0.87/1.03  thf('59', plain,
% 0.87/1.03      (![X12 : $i, X13 : $i]:
% 0.87/1.03         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.87/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.03  thf('60', plain,
% 0.87/1.03      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.87/1.03         = (k1_tarski @ sk_B))),
% 0.87/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.87/1.03  thf('61', plain,
% 0.87/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.03  thf('62', plain,
% 0.87/1.03      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.87/1.03      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.87/1.03  thf('63', plain,
% 0.87/1.03      (![X12 : $i, X13 : $i]:
% 0.87/1.03         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.87/1.03      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.87/1.03  thf('64', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.87/1.03           = (k3_xboole_0 @ X0 @ X1))),
% 0.87/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.87/1.03  thf('65', plain,
% 0.87/1.03      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.87/1.03  thf('66', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.87/1.03           = (k3_xboole_0 @ X0 @ X1))),
% 0.87/1.03      inference('demod', [status(thm)], ['64', '65'])).
% 0.87/1.03  thf('67', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ X0 @ X1)
% 0.87/1.03           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['17', '18'])).
% 0.87/1.03  thf('68', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.87/1.03           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['66', '67'])).
% 0.87/1.03  thf('69', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.87/1.03      inference('demod', [status(thm)], ['24', '27', '30'])).
% 0.87/1.03  thf('70', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.87/1.03      inference('demod', [status(thm)], ['68', '69'])).
% 0.87/1.03  thf('71', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['61', '70'])).
% 0.87/1.03  thf('72', plain,
% 0.87/1.03      (![X18 : $i, X19 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ X18 @ X19)
% 0.87/1.03           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.87/1.03  thf('73', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.87/1.03           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['71', '72'])).
% 0.87/1.03  thf('74', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.87/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.87/1.03  thf('75', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.87/1.03      inference('demod', [status(thm)], ['73', '74'])).
% 0.87/1.03  thf('76', plain,
% 0.87/1.03      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ sk_B))
% 0.87/1.03         = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('sup+', [status(thm)], ['60', '75'])).
% 0.87/1.03  thf('77', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.87/1.03           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['45', '46'])).
% 0.87/1.03  thf('78', plain,
% 0.87/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.87/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.87/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.87/1.03  thf('79', plain,
% 0.87/1.03      (((k1_enumset1 @ sk_C @ sk_D @ sk_B) = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.87/1.03  thf('80', plain,
% 0.87/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_enumset1 @ X33 @ X34 @ X35)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.87/1.03  thf('81', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.87/1.03      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.87/1.03  thf('82', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.87/1.03           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['80', '81'])).
% 0.87/1.03  thf('83', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ X0))
% 0.87/1.03           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B))),
% 0.87/1.03      inference('sup+', [status(thm)], ['79', '82'])).
% 0.87/1.03  thf('84', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.87/1.03           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['45', '46'])).
% 0.87/1.03  thf('85', plain,
% 0.87/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.87/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.87/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.87/1.03  thf('86', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k1_enumset1 @ sk_C @ sk_D @ X0)
% 0.87/1.03           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B))),
% 0.87/1.03      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.87/1.03  thf('87', plain,
% 0.87/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.87/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.87/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.87/1.03  thf('88', plain,
% 0.87/1.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.87/1.03           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.87/1.03  thf('89', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.87/1.03           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 0.87/1.03              (k1_tarski @ X3)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['87', '88'])).
% 0.87/1.03  thf('90', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k2_enumset1 @ sk_C @ sk_D @ sk_B @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k1_enumset1 @ sk_C @ sk_D @ sk_C) @ 
% 0.87/1.03              (k1_tarski @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['86', '89'])).
% 0.87/1.03  thf('91', plain,
% 0.87/1.03      (((k1_enumset1 @ sk_C @ sk_D @ sk_B) = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.87/1.03  thf('92', plain,
% 0.87/1.03      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.87/1.03           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.87/1.03  thf('93', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k2_enumset1 @ sk_C @ sk_D @ sk_B @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k1_tarski @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['91', '92'])).
% 0.87/1.03  thf('94', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.87/1.03           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['45', '46'])).
% 0.87/1.03  thf('95', plain,
% 0.87/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.87/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.87/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.87/1.03  thf('96', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k2_enumset1 @ sk_C @ sk_D @ sk_B @ X0)
% 0.87/1.03           = (k1_enumset1 @ sk_C @ sk_D @ X0))),
% 0.87/1.03      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.87/1.03  thf('97', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.87/1.03         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.87/1.03           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.87/1.03      inference('sup+', [status(thm)], ['80', '81'])).
% 0.87/1.03  thf('98', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k1_enumset1 @ sk_C @ sk_D @ X0)
% 0.87/1.03           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_C))),
% 0.87/1.03      inference('demod', [status(thm)], ['90', '96', '97'])).
% 0.87/1.03  thf('99', plain,
% 0.87/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.87/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.87/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.87/1.03  thf('100', plain,
% 0.87/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_enumset1 @ X33 @ X34 @ X35)))),
% 0.87/1.03      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.87/1.03  thf('101', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.87/1.03              (k2_enumset1 @ X2 @ X2 @ X1 @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['99', '100'])).
% 0.87/1.03  thf('102', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_C)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.87/1.03              (k1_enumset1 @ sk_C @ sk_D @ sk_C)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['98', '101'])).
% 0.87/1.03  thf('103', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k1_enumset1 @ sk_C @ sk_D @ X0)
% 0.87/1.03           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_C))),
% 0.87/1.03      inference('demod', [status(thm)], ['90', '96', '97'])).
% 0.87/1.03  thf('104', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k1_enumset1 @ sk_C @ sk_D @ X0)
% 0.87/1.03           = (k2_enumset1 @ X0 @ sk_C @ sk_D @ sk_B))),
% 0.87/1.03      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.87/1.03  thf('105', plain,
% 0.87/1.03      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.87/1.03           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.87/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.87/1.03  thf('106', plain,
% 0.87/1.03      (((k1_enumset1 @ sk_C @ sk_D @ sk_C) = (k1_enumset1 @ sk_C @ sk_D @ sk_B))),
% 0.87/1.03      inference('sup+', [status(thm)], ['104', '105'])).
% 0.87/1.03  thf('107', plain,
% 0.87/1.03      (((k1_enumset1 @ sk_C @ sk_D @ sk_B) = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.87/1.03  thf('108', plain,
% 0.87/1.03      (((k1_enumset1 @ sk_C @ sk_D @ sk_C) = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('sup+', [status(thm)], ['106', '107'])).
% 0.87/1.03  thf('109', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.87/1.03           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.87/1.03      inference('sup+', [status(thm)], ['38', '39'])).
% 0.87/1.03  thf('110', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((k1_enumset1 @ sk_C @ sk_D @ X0)
% 0.87/1.03           = (k2_enumset1 @ X0 @ sk_C @ sk_C @ sk_D))),
% 0.87/1.03      inference('demod', [status(thm)], ['102', '103', '108', '109'])).
% 0.87/1.03  thf('111', plain,
% 0.87/1.03      (((k1_enumset1 @ sk_C @ sk_D @ sk_A) = (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('demod', [status(thm)], ['41', '110'])).
% 0.87/1.03  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.87/1.03  thf(zf_stmt_3, axiom,
% 0.87/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.87/1.03       ( ![E:$i]:
% 0.87/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.87/1.03  thf('112', plain,
% 0.87/1.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.87/1.03         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.87/1.03          | (r2_hidden @ X25 @ X29)
% 0.87/1.03          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.87/1.03  thf('113', plain,
% 0.87/1.03      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.87/1.03         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 0.87/1.03          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 0.87/1.03      inference('simplify', [status(thm)], ['112'])).
% 0.87/1.03  thf('114', plain,
% 0.87/1.03      (![X0 : $i]:
% 0.87/1.03         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D))
% 0.87/1.03          | (zip_tseitin_0 @ X0 @ sk_A @ sk_D @ sk_C))),
% 0.87/1.03      inference('sup+', [status(thm)], ['111', '113'])).
% 0.87/1.03  thf('115', plain,
% 0.87/1.03      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.87/1.03         (((X21) != (X22)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.03  thf('116', plain,
% 0.87/1.03      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.87/1.03         ~ (zip_tseitin_0 @ X22 @ X22 @ X23 @ X20)),
% 0.87/1.03      inference('simplify', [status(thm)], ['115'])).
% 0.87/1.03  thf('117', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C @ sk_D))),
% 0.87/1.03      inference('sup-', [status(thm)], ['114', '116'])).
% 0.87/1.03  thf('118', plain,
% 0.87/1.03      (![X41 : $i, X42 : $i]:
% 0.87/1.03         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.87/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.87/1.03  thf('119', plain,
% 0.87/1.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.87/1.03         (~ (r2_hidden @ X30 @ X29)
% 0.87/1.03          | ~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 0.87/1.03          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.87/1.03  thf('120', plain,
% 0.87/1.03      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 0.87/1.03         (~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 0.87/1.03          | ~ (r2_hidden @ X30 @ (k1_enumset1 @ X28 @ X27 @ X26)))),
% 0.87/1.03      inference('simplify', [status(thm)], ['119'])).
% 0.87/1.03  thf('121', plain,
% 0.87/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.03         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.87/1.03          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.87/1.03      inference('sup-', [status(thm)], ['118', '120'])).
% 0.87/1.03  thf('122', plain, (~ (zip_tseitin_0 @ sk_A @ sk_D @ sk_C @ sk_C)),
% 0.87/1.03      inference('sup-', [status(thm)], ['117', '121'])).
% 0.87/1.03  thf('123', plain,
% 0.87/1.03      ((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_D)))),
% 0.87/1.03      inference('sup-', [status(thm)], ['0', '122'])).
% 0.87/1.03  thf('124', plain, ((((sk_A) = (sk_D)) | ((sk_A) = (sk_C)))),
% 0.87/1.03      inference('simplify', [status(thm)], ['123'])).
% 0.87/1.03  thf('125', plain, (((sk_A) != (sk_C))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.87/1.03  thf('126', plain, (((sk_A) != (sk_D))),
% 0.87/1.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.87/1.03  thf('127', plain, ($false),
% 0.87/1.03      inference('simplify_reflect-', [status(thm)], ['124', '125', '126'])).
% 0.87/1.03  
% 0.87/1.03  % SZS output end Refutation
% 0.87/1.03  
% 0.87/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
