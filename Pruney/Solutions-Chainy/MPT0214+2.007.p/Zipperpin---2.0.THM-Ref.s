%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PhR5T8Q90h

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:45 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 133 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  731 ( 956 expanded)
%              Number of equality atoms :   84 ( 113 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','30'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['11','36','37'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('39',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('41',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('44',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('45',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X23 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PhR5T8Q90h
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 969 iterations in 0.484s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(d1_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.94       ( ![E:$i]:
% 0.75/0.94         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.94           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, axiom,
% 0.75/0.94    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.94     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.94       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.75/0.94          | ((X22) = (X23))
% 0.75/0.94          | ((X22) = (X24))
% 0.75/0.94          | ((X22) = (X25)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf(t6_zfmisc_1, conjecture,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.75/0.94       ( ( A ) = ( B ) ) ))).
% 0.75/0.94  thf(zf_stmt_1, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i]:
% 0.75/0.94        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.75/0.94          ( ( A ) = ( B ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.75/0.94  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf(t28_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.94  thf('2', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.75/0.94      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/0.94         = (k1_tarski @ sk_A))),
% 0.75/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.94  thf(t100_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.94  thf('4', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X7 @ X8)
% 0.75/0.94           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('5', plain,
% 0.75/0.94      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/0.94         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['3', '4'])).
% 0.75/0.94  thf(idempotence_k3_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/0.94  thf('6', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.75/0.94      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X7 @ X8)
% 0.75/0.94           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['6', '7'])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.75/0.94         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.75/0.94      inference('demod', [status(thm)], ['5', '8'])).
% 0.75/0.94  thf(t98_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.75/0.94  thf('10', plain,
% 0.75/0.94      (![X19 : $i, X20 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X19 @ X20)
% 0.75/0.94           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.75/0.94         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.75/0.94            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.75/0.94      inference('sup+', [status(thm)], ['9', '10'])).
% 0.75/0.94  thf('12', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['6', '7'])).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['6', '7'])).
% 0.75/0.94  thf(t91_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.94       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.75/0.94  thf('14', plain,
% 0.75/0.94      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.75/0.94           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.75/0.94           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['13', '14'])).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.75/0.94           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['12', '15'])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      (![X19 : $i, X20 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X19 @ X20)
% 0.75/0.94           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.94  thf(idempotence_k2_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/0.94  thf('18', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ X5) = (X5))),
% 0.75/0.94      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.75/0.94  thf(t79_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.75/0.94      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.75/0.94  thf(d7_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.94       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (![X2 : $i, X3 : $i]:
% 0.75/0.94         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.75/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.94  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/0.94  thf('25', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X7 @ X8)
% 0.75/0.94           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['24', '25'])).
% 0.75/0.94  thf(t5_boole, axiom,
% 0.75/0.94    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.94  thf('27', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t5_boole])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['26', '27'])).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      (![X19 : $i, X20 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ X19 @ X20)
% 0.75/0.94           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.75/0.94           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['28', '29'])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['19', '30'])).
% 0.75/0.94  thf(t21_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X9 : $i, X10 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.75/0.94      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.75/0.94           = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['31', '32'])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['22', '23'])).
% 0.75/0.94  thf('36', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.75/0.94  thf('37', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.75/0.94      inference('cnf', [status(esa)], [t5_boole])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.75/0.94         = (k1_tarski @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['11', '36', '37'])).
% 0.75/0.94  thf(t69_enumset1, axiom,
% 0.75/0.94    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.75/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.94  thf(t70_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X41 : $i, X42 : $i]:
% 0.75/0.94         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.94  thf(t46_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.75/0.94       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.75/0.94         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.75/0.94           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.75/0.94           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['40', '41'])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.75/0.94           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['39', '42'])).
% 0.75/0.94  thf(t71_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.75/0.94         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.75/0.94           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.75/0.94      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      (![X41 : $i, X42 : $i]:
% 0.75/0.94         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['44', '45'])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k2_tarski @ X0 @ X1)
% 0.75/0.94           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['43', '46'])).
% 0.75/0.94  thf('48', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.75/0.94      inference('demod', [status(thm)], ['38', '47'])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (![X41 : $i, X42 : $i]:
% 0.75/0.94         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.94  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_3, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.94       ( ![E:$i]:
% 0.75/0.94         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.75/0.94          | (r2_hidden @ X26 @ X30)
% 0.75/0.94          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.94  thf('51', plain,
% 0.75/0.94      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.75/0.94         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 0.75/0.94          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 0.75/0.94      inference('simplify', [status(thm)], ['50'])).
% 0.75/0.94  thf('52', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.94          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['49', '51'])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.94         (((X22) != (X23)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.75/0.94         ~ (zip_tseitin_0 @ X23 @ X23 @ X24 @ X21)),
% 0.75/0.94      inference('simplify', [status(thm)], ['53'])).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['52', '54'])).
% 0.75/0.94  thf('56', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.75/0.94      inference('sup+', [status(thm)], ['48', '55'])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.75/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.94  thf('58', plain,
% 0.75/0.94      (![X41 : $i, X42 : $i]:
% 0.75/0.94         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.75/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X31 @ X30)
% 0.75/0.94          | ~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.75/0.94          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.94  thf('60', plain,
% 0.75/0.94      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.75/0.94         (~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 0.75/0.94          | ~ (r2_hidden @ X31 @ (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['59'])).
% 0.75/0.94  thf('61', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.94          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['58', '60'])).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.94          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['57', '61'])).
% 0.75/0.94  thf('63', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.75/0.94      inference('sup-', [status(thm)], ['56', '62'])).
% 0.75/0.94  thf('64', plain,
% 0.75/0.94      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['0', '63'])).
% 0.75/0.94  thf('65', plain, (((sk_A) = (sk_B))),
% 0.75/0.94      inference('simplify', [status(thm)], ['64'])).
% 0.75/0.94  thf('66', plain, (((sk_A) != (sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.94  thf('67', plain, ($false),
% 0.75/0.94      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
