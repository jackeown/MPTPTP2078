%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zXvutZfvVl

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:07 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  236 (6807 expanded)
%              Number of leaves         :   32 (2351 expanded)
%              Depth                    :   48
%              Number of atoms          : 2029 (53274 expanded)
%              Number of equality atoms :  204 (6441 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( X24 = X25 )
      | ( X24 = X26 )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

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

thf('12',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['11','23'])).

thf('25',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['10','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('57',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','55','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('61',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','57','58','59','60'])).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['9','65'])).

thf('67',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','57','58','59','60'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','55','56'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('71',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('73',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','55','56'])).

thf('82',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('85',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('88',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['82','93'])).

thf('95',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['81','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','55','56'])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('102',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('103',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('106',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['78','79','80','103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('112',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('114',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['71','112','113'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('115',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('116',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('117',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','119'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('121',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('122',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('123',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('124',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_B ) )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','125'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
      | ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','55','56'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('146',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('147',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('148',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['146','148'])).

thf('150',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['149','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['145','152'])).

thf('154',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['144','153'])).

thf('155',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('156',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['11','23'])).

thf('160',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['78','79','80','103','104','105'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['140','143'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('164',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['140','143'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('166',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['158','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['157','167'])).

thf('169',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('170',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','55','56'])).

thf('173',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('178',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','55','56'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177','180'])).

thf('182',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['171','185'])).

thf('187',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    r2_hidden @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['154','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['37','48'])).

thf('196',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','125'])).

thf('198',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','198'])).

thf('200',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('202',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['200','201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zXvutZfvVl
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.90  % Solved by: fo/fo7.sh
% 0.66/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.90  % done 914 iterations in 0.452s
% 0.66/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.90  % SZS output start Refutation
% 0.66/0.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.66/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.66/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.90  thf(d1_enumset1, axiom,
% 0.66/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.90     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.66/0.90       ( ![E:$i]:
% 0.66/0.90         ( ( r2_hidden @ E @ D ) <=>
% 0.66/0.90           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.66/0.90  thf(zf_stmt_0, axiom,
% 0.66/0.90    (![E:$i,C:$i,B:$i,A:$i]:
% 0.66/0.90     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.66/0.90       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.66/0.90  thf('0', plain,
% 0.66/0.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.90         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.66/0.90          | ((X24) = (X25))
% 0.66/0.90          | ((X24) = (X26))
% 0.66/0.90          | ((X24) = (X27)))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('1', plain,
% 0.66/0.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.90         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.66/0.90          | ((X24) = (X25))
% 0.66/0.90          | ((X24) = (X26))
% 0.66/0.90          | ((X24) = (X27)))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf('2', plain,
% 0.66/0.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.90         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.66/0.90          | ((X24) = (X25))
% 0.66/0.90          | ((X24) = (X26))
% 0.66/0.90          | ((X24) = (X27)))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.90  thf(t1_boole, axiom,
% 0.66/0.90    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.90  thf('3', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.66/0.90      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.90  thf(t7_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.66/0.90  thf('4', plain,
% 0.66/0.90      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.66/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.90  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.66/0.90      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.90  thf(t28_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.90  thf('6', plain,
% 0.66/0.90      (![X11 : $i, X12 : $i]:
% 0.66/0.90         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.66/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.90  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.66/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.90  thf(t100_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.90  thf('8', plain,
% 0.66/0.90      (![X8 : $i, X9 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.90  thf('9', plain,
% 0.66/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['7', '8'])).
% 0.66/0.90  thf('10', plain,
% 0.66/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['7', '8'])).
% 0.66/0.90  thf(commutativity_k5_xboole_0, axiom,
% 0.66/0.90    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.66/0.90  thf('11', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf(t13_zfmisc_1, conjecture,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.66/0.90         ( k1_tarski @ A ) ) =>
% 0.66/0.90       ( ( A ) = ( B ) ) ))).
% 0.66/0.90  thf(zf_stmt_1, negated_conjecture,
% 0.66/0.90    (~( ![A:$i,B:$i]:
% 0.66/0.90        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.66/0.90            ( k1_tarski @ A ) ) =>
% 0.66/0.90          ( ( A ) = ( B ) ) ) )),
% 0.66/0.90    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.66/0.90  thf('12', plain,
% 0.66/0.90      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.66/0.90         = (k1_tarski @ sk_A))),
% 0.66/0.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.90  thf(t95_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( k3_xboole_0 @ A @ B ) =
% 0.66/0.90       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.66/0.90  thf('13', plain,
% 0.66/0.90      (![X19 : $i, X20 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ X19 @ X20)
% 0.66/0.90           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.66/0.90              (k2_xboole_0 @ X19 @ X20)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.66/0.90  thf('14', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf('15', plain,
% 0.66/0.90      (![X19 : $i, X20 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ X19 @ X20)
% 0.66/0.90           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 0.66/0.90              (k5_xboole_0 @ X19 @ X20)))),
% 0.66/0.90      inference('demod', [status(thm)], ['13', '14'])).
% 0.66/0.90  thf('16', plain,
% 0.66/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 0.66/0.90      inference('sup+', [status(thm)], ['12', '15'])).
% 0.66/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.90  thf('17', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('18', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf('19', plain,
% 0.66/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90            (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.66/0.90      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.66/0.90  thf(t91_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i,C:$i]:
% 0.66/0.90     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.90       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.66/0.90  thf('20', plain,
% 0.66/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.90           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.90  thf('21', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ 
% 0.66/0.90           (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.66/0.90           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90              (k5_xboole_0 @ 
% 0.66/0.90               (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['19', '20'])).
% 0.66/0.90  thf('22', plain,
% 0.66/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.90           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.90  thf('23', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ 
% 0.66/0.90           (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.66/0.90           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90               (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))),
% 0.66/0.90      inference('demod', [status(thm)], ['21', '22'])).
% 0.66/0.90  thf('24', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ 
% 0.66/0.90           (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.66/0.90           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90               (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)))))),
% 0.66/0.90      inference('sup+', [status(thm)], ['11', '23'])).
% 0.66/0.90  thf('25', plain,
% 0.66/0.90      (((k5_xboole_0 @ 
% 0.66/0.90         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.90         (k1_tarski @ sk_A))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90            (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90             (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))))),
% 0.66/0.90      inference('sup+', [status(thm)], ['10', '24'])).
% 0.66/0.90  thf('26', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf('27', plain,
% 0.66/0.90      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90            (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90             (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))))),
% 0.66/0.90      inference('demod', [status(thm)], ['25', '26'])).
% 0.66/0.90  thf('28', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.66/0.90      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.90  thf('29', plain,
% 0.66/0.90      (![X19 : $i, X20 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ X19 @ X20)
% 0.66/0.90           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 0.66/0.90              (k5_xboole_0 @ X19 @ X20)))),
% 0.66/0.90      inference('demod', [status(thm)], ['13', '14'])).
% 0.66/0.90  thf('30', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.66/0.90           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['28', '29'])).
% 0.66/0.90  thf(t5_boole, axiom,
% 0.66/0.90    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.90  thf('31', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.66/0.90      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.90  thf('32', plain,
% 0.66/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.90      inference('demod', [status(thm)], ['30', '31'])).
% 0.66/0.90  thf(t98_xboole_1, axiom,
% 0.66/0.90    (![A:$i,B:$i]:
% 0.66/0.90     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.66/0.90  thf('33', plain,
% 0.66/0.90      (![X21 : $i, X22 : $i]:
% 0.66/0.90         ((k2_xboole_0 @ X21 @ X22)
% 0.66/0.90           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.90  thf('34', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf('35', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.66/0.90      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.90  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.90  thf('37', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['33', '36'])).
% 0.66/0.90  thf('38', plain,
% 0.66/0.90      (![X8 : $i, X9 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.90  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.90  thf('40', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['38', '39'])).
% 0.66/0.90  thf('41', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('42', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['40', '41'])).
% 0.66/0.90  thf('43', plain,
% 0.66/0.90      (![X8 : $i, X9 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.90  thf('44', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.66/0.90           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['42', '43'])).
% 0.66/0.90  thf('45', plain,
% 0.66/0.90      (![X21 : $i, X22 : $i]:
% 0.66/0.90         ((k2_xboole_0 @ X21 @ X22)
% 0.66/0.90           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.90  thf('46', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.90      inference('demod', [status(thm)], ['44', '45'])).
% 0.66/0.90  thf('47', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.66/0.90      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.90  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['46', '47'])).
% 0.66/0.90  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.90      inference('demod', [status(thm)], ['37', '48'])).
% 0.66/0.90  thf('50', plain,
% 0.66/0.90      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.66/0.90      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.90  thf('51', plain,
% 0.66/0.90      (![X11 : $i, X12 : $i]:
% 0.66/0.90         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.66/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.90  thf('52', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]:
% 0.66/0.90         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.66/0.90      inference('sup-', [status(thm)], ['50', '51'])).
% 0.66/0.90  thf('53', plain,
% 0.66/0.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['49', '52'])).
% 0.66/0.90  thf('54', plain,
% 0.66/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.90  thf('55', plain,
% 0.66/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['53', '54'])).
% 0.66/0.90  thf('56', plain,
% 0.66/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['7', '8'])).
% 0.66/0.90  thf('57', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.90      inference('demod', [status(thm)], ['32', '55', '56'])).
% 0.66/0.90  thf('58', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.90  thf('60', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf('61', plain,
% 0.66/0.90      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.66/0.90      inference('demod', [status(thm)], ['27', '57', '58', '59', '60'])).
% 0.66/0.90  thf('62', plain,
% 0.66/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.90           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.90  thf('63', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ 
% 0.66/0.90           (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.66/0.90           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90              (k5_xboole_0 @ 
% 0.66/0.90               (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['61', '62'])).
% 0.66/0.90  thf('64', plain,
% 0.66/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.90           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.90  thf('65', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90           (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.66/0.90           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90              (k5_xboole_0 @ 
% 0.66/0.90               (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)))),
% 0.66/0.90      inference('demod', [status(thm)], ['63', '64'])).
% 0.66/0.90  thf('66', plain,
% 0.66/0.90      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90         (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90          (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90            (k4_xboole_0 @ 
% 0.66/0.90             (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.90             (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))))),
% 0.66/0.90      inference('sup+', [status(thm)], ['9', '65'])).
% 0.66/0.90  thf('67', plain,
% 0.66/0.90      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.66/0.90      inference('demod', [status(thm)], ['27', '57', '58', '59', '60'])).
% 0.66/0.90  thf('68', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.90      inference('demod', [status(thm)], ['32', '55', '56'])).
% 0.66/0.90  thf('69', plain,
% 0.66/0.90      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.90      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.90  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.90      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.90  thf('71', plain,
% 0.66/0.90      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90         (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.90         = (k1_tarski @ sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.66/0.90  thf('72', plain,
% 0.66/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90            (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.66/0.90      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.66/0.90  thf('73', plain,
% 0.66/0.90      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90         (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.90         = (k1_tarski @ sk_A))),
% 0.66/0.90      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.66/0.90  thf('74', plain,
% 0.66/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.90           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.90  thf('75', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.90           = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90              (k5_xboole_0 @ 
% 0.66/0.90               (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)))),
% 0.66/0.90      inference('sup+', [status(thm)], ['73', '74'])).
% 0.66/0.90  thf('76', plain,
% 0.66/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.90           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.90  thf('77', plain,
% 0.66/0.90      (![X0 : $i]:
% 0.66/0.90         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.90           = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90               (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))),
% 0.66/0.90      inference('demod', [status(thm)], ['75', '76'])).
% 0.66/0.90  thf('78', plain,
% 0.66/0.90      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90         (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90            (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.90             (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))))),
% 0.66/0.90      inference('sup+', [status(thm)], ['72', '77'])).
% 0.66/0.90  thf('79', plain,
% 0.66/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.66/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.90            (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.66/0.90      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.66/0.90  thf('80', plain,
% 0.66/0.90      (![X8 : $i, X9 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.90  thf('81', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.90      inference('demod', [status(thm)], ['32', '55', '56'])).
% 0.66/0.90  thf('82', plain,
% 0.66/0.90      (![X8 : $i, X9 : $i]:
% 0.66/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('83', plain,
% 0.66/0.91      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.66/0.91         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91            (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))))),
% 0.66/0.91      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.66/0.91  thf('84', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ 
% 0.66/0.91           (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.91               (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))),
% 0.66/0.91      inference('demod', [status(thm)], ['21', '22'])).
% 0.66/0.91  thf('85', plain,
% 0.66/0.91      (((k5_xboole_0 @ 
% 0.66/0.91         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.91         (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.91         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91            (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.91             (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))))),
% 0.66/0.91      inference('sup+', [status(thm)], ['83', '84'])).
% 0.66/0.91  thf('86', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.91           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('87', plain,
% 0.66/0.91      (![X21 : $i, X22 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X21 @ X22)
% 0.66/0.91           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.91  thf('88', plain,
% 0.66/0.91      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.66/0.91         = (k1_tarski @ sk_A))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.91  thf('89', plain,
% 0.66/0.91      (((k5_xboole_0 @ 
% 0.66/0.91         (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.91         (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))
% 0.66/0.91         = (k1_tarski @ sk_A))),
% 0.66/0.91      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.66/0.91  thf('90', plain,
% 0.66/0.91      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.91           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.91  thf('91', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ 
% 0.66/0.91              (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.91              (k5_xboole_0 @ 
% 0.66/0.91               (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['89', '90'])).
% 0.66/0.91  thf('92', plain,
% 0.66/0.91      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.91           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.91  thf('93', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ 
% 0.66/0.91              (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.91              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.91               (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))))),
% 0.66/0.91      inference('demod', [status(thm)], ['91', '92'])).
% 0.66/0.91  thf('94', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91           (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.66/0.91           = (k5_xboole_0 @ 
% 0.66/0.91              (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.91              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.91               (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))))),
% 0.66/0.91      inference('sup+', [status(thm)], ['82', '93'])).
% 0.66/0.91  thf('95', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.91           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('96', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ 
% 0.66/0.91              (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.91              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.91               (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))))),
% 0.66/0.91      inference('demod', [status(thm)], ['94', '95'])).
% 0.66/0.91  thf('97', plain,
% 0.66/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.66/0.91         = (k5_xboole_0 @ 
% 0.66/0.91            (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.66/0.91            (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['81', '96'])).
% 0.66/0.91  thf('98', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['32', '55', '56'])).
% 0.66/0.91  thf('99', plain,
% 0.66/0.91      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.91  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf('101', plain,
% 0.66/0.91      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.91  thf('102', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.91           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('103', plain,
% 0.66/0.91      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('demod', [status(thm)], ['97', '98', '99', '100', '101', '102'])).
% 0.66/0.91  thf('104', plain,
% 0.66/0.91      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.91  thf('105', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf('106', plain,
% 0.66/0.91      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.66/0.91         = (k1_tarski @ sk_B))),
% 0.66/0.91      inference('demod', [status(thm)], ['78', '79', '80', '103', '104', '105'])).
% 0.66/0.91  thf('107', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.91  thf('108', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.91           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('109', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['107', '108'])).
% 0.66/0.91  thf('110', plain,
% 0.66/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.66/0.91         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['106', '109'])).
% 0.66/0.91  thf('111', plain,
% 0.66/0.91      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.91  thf('112', plain,
% 0.66/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.66/0.91         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('demod', [status(thm)], ['110', '111'])).
% 0.66/0.91  thf('113', plain,
% 0.66/0.91      (![X21 : $i, X22 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X21 @ X22)
% 0.66/0.91           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.91  thf('114', plain,
% 0.66/0.91      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.66/0.91         = (k1_tarski @ sk_A))),
% 0.66/0.91      inference('demod', [status(thm)], ['71', '112', '113'])).
% 0.66/0.91  thf(d3_tarski, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.91  thf('115', plain,
% 0.66/0.91      (![X5 : $i, X7 : $i]:
% 0.66/0.91         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('116', plain,
% 0.66/0.91      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.66/0.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.91  thf('117', plain,
% 0.66/0.91      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X4 @ X5)
% 0.66/0.91          | (r2_hidden @ X4 @ X6)
% 0.66/0.91          | ~ (r1_tarski @ X5 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('118', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['116', '117'])).
% 0.66/0.91  thf('119', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((r1_tarski @ X0 @ X1)
% 0.66/0.91          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['115', '118'])).
% 0.66/0.91  thf('120', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ (k1_tarski @ sk_A))
% 0.66/0.91          | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['114', '119'])).
% 0.66/0.91  thf(t69_enumset1, axiom,
% 0.66/0.91    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.66/0.91  thf('121', plain,
% 0.66/0.91      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.66/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.91  thf(t70_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.66/0.91  thf('122', plain,
% 0.66/0.91      (![X36 : $i, X37 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.66/0.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.91  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.66/0.91  thf(zf_stmt_3, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.66/0.91       ( ![E:$i]:
% 0.66/0.91         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.66/0.91  thf('123', plain,
% 0.66/0.91      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X33 @ X32)
% 0.66/0.91          | ~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.66/0.91          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.66/0.91  thf('124', plain,
% 0.66/0.91      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.66/0.91         (~ (zip_tseitin_0 @ X33 @ X29 @ X30 @ X31)
% 0.66/0.91          | ~ (r2_hidden @ X33 @ (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['123'])).
% 0.66/0.91  thf('125', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.66/0.91          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['122', '124'])).
% 0.66/0.91  thf('126', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.66/0.91          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['121', '125'])).
% 0.66/0.91  thf('127', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.66/0.91          | ~ (zip_tseitin_0 @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ sk_A @ 
% 0.66/0.91               sk_A @ sk_A))),
% 0.66/0.91      inference('sup-', [status(thm)], ['120', '126'])).
% 0.66/0.91  thf('128', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A))
% 0.66/0.91          | ((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A))
% 0.66/0.91          | ((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A))
% 0.66/0.91          | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['2', '127'])).
% 0.66/0.91  thf('129', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.66/0.91          | ((sk_C @ X0 @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['128'])).
% 0.66/0.91  thf('130', plain,
% 0.66/0.91      (![X5 : $i, X7 : $i]:
% 0.66/0.91         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('131', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.66/0.91          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['121', '125'])).
% 0.66/0.91  thf('132', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.66/0.91          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['130', '131'])).
% 0.66/0.91  thf('133', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)
% 0.66/0.91          | (r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.66/0.91          | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['129', '132'])).
% 0.66/0.91  thf('134', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((r1_tarski @ (k1_tarski @ sk_B) @ X0)
% 0.66/0.91          | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))),
% 0.66/0.91      inference('simplify', [status(thm)], ['133'])).
% 0.66/0.91  thf('135', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         (((sk_A) = (sk_B))
% 0.66/0.91          | ((sk_A) = (sk_B))
% 0.66/0.91          | ((sk_A) = (sk_B))
% 0.66/0.91          | (r1_tarski @ (k1_tarski @ sk_B) @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['1', '134'])).
% 0.66/0.91  thf('136', plain,
% 0.66/0.91      (![X0 : $i]: ((r1_tarski @ (k1_tarski @ sk_B) @ X0) | ((sk_A) = (sk_B)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['135'])).
% 0.66/0.91  thf('137', plain, (((sk_A) != (sk_B))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.91  thf('138', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_B) @ X0)),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['136', '137'])).
% 0.66/0.91  thf('139', plain,
% 0.66/0.91      (![X11 : $i, X12 : $i]:
% 0.66/0.91         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.66/0.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.91  thf('140', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ (k1_tarski @ sk_B) @ X0) = (k1_tarski @ sk_B))),
% 0.66/0.91      inference('sup-', [status(thm)], ['138', '139'])).
% 0.66/0.91  thf('141', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['32', '55', '56'])).
% 0.66/0.91  thf('142', plain,
% 0.66/0.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['53', '54'])).
% 0.66/0.91  thf('143', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['141', '142'])).
% 0.66/0.91  thf('144', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['140', '143'])).
% 0.66/0.91  thf('145', plain,
% 0.66/0.91      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.66/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.91  thf('146', plain,
% 0.66/0.91      (![X36 : $i, X37 : $i]:
% 0.66/0.91         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.66/0.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.91  thf('147', plain,
% 0.66/0.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.66/0.91         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.66/0.91          | (r2_hidden @ X28 @ X32)
% 0.66/0.91          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.66/0.91  thf('148', plain,
% 0.66/0.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.91         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 0.66/0.91          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 0.66/0.91      inference('simplify', [status(thm)], ['147'])).
% 0.66/0.91  thf('149', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.66/0.91          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.66/0.91      inference('sup+', [status(thm)], ['146', '148'])).
% 0.66/0.91  thf('150', plain,
% 0.66/0.91      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.66/0.91         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('151', plain,
% 0.66/0.91      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.66/0.91         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 0.66/0.91      inference('simplify', [status(thm)], ['150'])).
% 0.66/0.91  thf('152', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['149', '151'])).
% 0.66/0.91  thf('153', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['145', '152'])).
% 0.66/0.91  thf('154', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.66/0.91      inference('sup+', [status(thm)], ['144', '153'])).
% 0.66/0.91  thf('155', plain,
% 0.66/0.91      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.91  thf('156', plain,
% 0.66/0.91      (![X19 : $i, X20 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X19 @ X20)
% 0.66/0.91           = (k5_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 0.66/0.91              (k5_xboole_0 @ X19 @ X20)))),
% 0.66/0.91      inference('demod', [status(thm)], ['13', '14'])).
% 0.66/0.91  thf('157', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['155', '156'])).
% 0.66/0.91  thf('158', plain,
% 0.66/0.91      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.91           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.91  thf('159', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ 
% 0.66/0.91           (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.91               (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)))))),
% 0.66/0.91      inference('sup+', [status(thm)], ['11', '23'])).
% 0.66/0.91  thf('160', plain,
% 0.66/0.91      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.66/0.91         = (k1_tarski @ sk_B))),
% 0.66/0.91      inference('demod', [status(thm)], ['78', '79', '80', '103', '104', '105'])).
% 0.66/0.91  thf('161', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91              (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.66/0.91               (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)))))),
% 0.66/0.91      inference('demod', [status(thm)], ['159', '160'])).
% 0.66/0.91  thf('162', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['140', '143'])).
% 0.66/0.91  thf('163', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf('164', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['140', '143'])).
% 0.66/0.91  thf('165', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf('166', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((X0)
% 0.66/0.91           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91              (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 0.66/0.91      inference('demod', [status(thm)], ['161', '162', '163', '164', '165'])).
% 0.66/0.91  thf('167', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ X1 @ X0)
% 0.66/0.91           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)))))),
% 0.66/0.91      inference('sup+', [status(thm)], ['158', '166'])).
% 0.66/0.91  thf('168', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.66/0.91              (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['157', '167'])).
% 0.66/0.91  thf('169', plain,
% 0.66/0.91      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.91  thf('170', plain,
% 0.66/0.91      (![X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X8 @ X9)
% 0.66/0.91           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.91  thf('171', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.66/0.91           = (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.66/0.91  thf('172', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['32', '55', '56'])).
% 0.66/0.91  thf('173', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.66/0.91      inference('cnf', [status(esa)], [t1_boole])).
% 0.66/0.91  thf('174', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.66/0.91      inference('sup+', [status(thm)], ['172', '173'])).
% 0.66/0.91  thf('175', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['155', '156'])).
% 0.66/0.91  thf('176', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.66/0.91           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['174', '175'])).
% 0.66/0.91  thf('177', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['141', '142'])).
% 0.66/0.91  thf('178', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['32', '55', '56'])).
% 0.66/0.91  thf('179', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf('180', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.66/0.91      inference('sup+', [status(thm)], ['178', '179'])).
% 0.66/0.91  thf('181', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['176', '177', '180'])).
% 0.66/0.91  thf('182', plain,
% 0.66/0.91      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.66/0.91           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.91  thf('183', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.66/0.91           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['181', '182'])).
% 0.66/0.91  thf('184', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['34', '35'])).
% 0.66/0.91  thf('185', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['183', '184'])).
% 0.66/0.91  thf('186', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.91           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['171', '185'])).
% 0.66/0.91  thf('187', plain,
% 0.66/0.91      (![X21 : $i, X22 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ X21 @ X22)
% 0.66/0.91           = (k5_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.66/0.91  thf('188', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.91           = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('demod', [status(thm)], ['186', '187'])).
% 0.66/0.91  thf('189', plain,
% 0.66/0.91      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.66/0.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.91  thf('190', plain,
% 0.66/0.91      (![X0 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['188', '189'])).
% 0.66/0.91  thf('191', plain,
% 0.66/0.91      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X4 @ X5)
% 0.66/0.91          | (r2_hidden @ X4 @ X6)
% 0.66/0.91          | ~ (r1_tarski @ X5 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('192', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.66/0.91          | ~ (r2_hidden @ X1 @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['190', '191'])).
% 0.66/0.91  thf('193', plain,
% 0.66/0.91      ((r2_hidden @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['154', '192'])).
% 0.66/0.91  thf('194', plain,
% 0.66/0.91      (![X0 : $i]:
% 0.66/0.91         ((k2_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.66/0.91           = (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('demod', [status(thm)], ['186', '187'])).
% 0.66/0.91  thf('195', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['37', '48'])).
% 0.66/0.91  thf('196', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.66/0.91      inference('demod', [status(thm)], ['193', '194', '195'])).
% 0.66/0.91  thf('197', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.66/0.91          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['121', '125'])).
% 0.66/0.91  thf('198', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.66/0.91      inference('sup-', [status(thm)], ['196', '197'])).
% 0.66/0.91  thf('199', plain,
% 0.66/0.91      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['0', '198'])).
% 0.66/0.91  thf('200', plain, (((sk_B) = (sk_A))),
% 0.66/0.91      inference('simplify', [status(thm)], ['199'])).
% 0.66/0.91  thf('201', plain, (((sk_A) != (sk_B))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.91  thf('202', plain, ($false),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['200', '201'])).
% 0.66/0.91  
% 0.66/0.91  % SZS output end Refutation
% 0.66/0.91  
% 0.66/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
