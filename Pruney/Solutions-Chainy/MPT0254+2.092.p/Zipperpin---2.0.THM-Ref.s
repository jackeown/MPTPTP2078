%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JV7AyPpjwU

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:47 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  145 (1150 expanded)
%              Number of leaves         :   35 ( 409 expanded)
%              Depth                    :   21
%              Number of atoms          : 1064 (9090 expanded)
%              Number of equality atoms :  119 (1088 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','26','27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('63',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','53','60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('65',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('67',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','53','60','61','62'])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','53','60','61','62'])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('73',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('78',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('80',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('83',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['79','90'])).

thf('92',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','91'])).

thf('93',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('94',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
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

thf('95',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('99',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','100'])).

thf('102',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['92','101'])).

thf('103',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('104',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('106',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('107',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('sup-',[status(thm)],['102','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JV7AyPpjwU
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.71  % Solved by: fo/fo7.sh
% 0.48/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.71  % done 608 iterations in 0.250s
% 0.48/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.71  % SZS output start Refutation
% 0.48/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.48/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.48/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.71  thf(t49_zfmisc_1, conjecture,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.48/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.71    (~( ![A:$i,B:$i]:
% 0.48/0.71        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.48/0.71    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.48/0.71  thf('0', plain,
% 0.48/0.71      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.48/0.71  thf('1', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf(t94_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k2_xboole_0 @ A @ B ) =
% 0.48/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.71  thf('2', plain,
% 0.48/0.71      (![X22 : $i, X23 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.48/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.48/0.71              (k3_xboole_0 @ X22 @ X23)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.48/0.71  thf('3', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('4', plain,
% 0.48/0.71      (![X22 : $i, X23 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.48/0.71              (k5_xboole_0 @ X22 @ X23)))),
% 0.48/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('5', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['1', '4'])).
% 0.48/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.71  thf('6', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf('7', plain,
% 0.48/0.71      (![X22 : $i, X23 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.48/0.71              (k5_xboole_0 @ X22 @ X23)))),
% 0.48/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('8', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['6', '7'])).
% 0.48/0.71  thf('9', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['5', '8'])).
% 0.48/0.71  thf('10', plain,
% 0.48/0.71      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['0', '9'])).
% 0.48/0.71  thf('11', plain,
% 0.48/0.71      (![X22 : $i, X23 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.48/0.71              (k5_xboole_0 @ X22 @ X23)))),
% 0.48/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('12', plain,
% 0.48/0.71      (![X22 : $i, X23 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.48/0.71              (k5_xboole_0 @ X22 @ X23)))),
% 0.48/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('13', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.48/0.71           = (k5_xboole_0 @ 
% 0.48/0.71              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.48/0.71              (k2_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.71  thf('14', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('15', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.48/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.48/0.71              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.48/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.71  thf('16', plain,
% 0.48/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.48/0.71         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.48/0.71            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['10', '15'])).
% 0.48/0.71  thf('17', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf(t5_boole, axiom,
% 0.48/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.71  thf('18', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.48/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.71  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.71  thf('20', plain,
% 0.48/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.48/0.71         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.48/0.71      inference('demod', [status(thm)], ['16', '19'])).
% 0.48/0.71  thf('21', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['1', '4'])).
% 0.48/0.71  thf('22', plain,
% 0.48/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.48/0.71         = (k5_xboole_0 @ 
% 0.48/0.71            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.48/0.71            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['20', '21'])).
% 0.48/0.71  thf(t91_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i]:
% 0.48/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.48/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.48/0.71  thf('23', plain,
% 0.48/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.48/0.71           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.71  thf('24', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf(t100_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.71  thf('25', plain,
% 0.48/0.71      (![X8 : $i, X9 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X8 @ X9)
% 0.48/0.71           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.71  thf('26', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.71  thf('27', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('28', plain,
% 0.48/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.48/0.71           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.71  thf('29', plain,
% 0.48/0.71      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.48/0.71         = (k5_xboole_0 @ sk_B @ 
% 0.48/0.71            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.48/0.71             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.48/0.71      inference('demod', [status(thm)], ['22', '23', '26', '27', '28'])).
% 0.48/0.71  thf('30', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf(t92_xboole_1, axiom,
% 0.48/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.48/0.71  thf('31', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.71  thf('32', plain,
% 0.48/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.48/0.71           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.71  thf('33', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['31', '32'])).
% 0.48/0.71  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.71  thf('35', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('demod', [status(thm)], ['33', '34'])).
% 0.48/0.71  thf('36', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['30', '35'])).
% 0.48/0.71  thf('37', plain,
% 0.48/0.71      (((sk_B)
% 0.48/0.71         = (k5_xboole_0 @ 
% 0.48/0.71            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.48/0.71             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.48/0.71            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.71             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.48/0.71      inference('sup+', [status(thm)], ['29', '36'])).
% 0.48/0.71  thf('38', plain,
% 0.48/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.48/0.71           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.71  thf(t2_boole, axiom,
% 0.48/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.48/0.71  thf('39', plain,
% 0.48/0.71      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.71  thf('40', plain,
% 0.48/0.71      (![X8 : $i, X9 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X8 @ X9)
% 0.48/0.71           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.48/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.71  thf('41', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['39', '40'])).
% 0.48/0.71  thf('42', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.48/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.71  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['41', '42'])).
% 0.48/0.71  thf(t36_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.48/0.71  thf('44', plain,
% 0.48/0.71      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.48/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.48/0.71  thf(t28_xboole_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.71  thf('45', plain,
% 0.48/0.71      (![X10 : $i, X11 : $i]:
% 0.48/0.71         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.48/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.71  thf('46', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.48/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['44', '45'])).
% 0.48/0.71  thf('47', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf('48', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.48/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.71  thf('49', plain,
% 0.48/0.71      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['43', '48'])).
% 0.48/0.71  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['41', '42'])).
% 0.48/0.71  thf('51', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['49', '50'])).
% 0.48/0.71  thf('52', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.71  thf('53', plain,
% 0.48/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['51', '52'])).
% 0.48/0.71  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['41', '42'])).
% 0.48/0.71  thf('55', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.48/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.71  thf('56', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.71  thf('57', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.48/0.71           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['55', '56'])).
% 0.48/0.71  thf('58', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.71  thf('59', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['57', '58'])).
% 0.48/0.71  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['54', '59'])).
% 0.48/0.71  thf('61', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.71  thf('63', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.48/0.71      inference('demod', [status(thm)], ['37', '38', '53', '60', '61', '62'])).
% 0.48/0.71  thf('64', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.48/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.71  thf('65', plain,
% 0.48/0.71      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.48/0.71         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.48/0.71      inference('sup+', [status(thm)], ['63', '64'])).
% 0.48/0.71  thf('66', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.71  thf('67', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.48/0.71      inference('demod', [status(thm)], ['37', '38', '53', '60', '61', '62'])).
% 0.48/0.71  thf('68', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.48/0.71      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.48/0.71  thf('69', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.71  thf('70', plain,
% 0.48/0.71      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.48/0.71         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.48/0.71      inference('sup+', [status(thm)], ['68', '69'])).
% 0.48/0.71  thf('71', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.48/0.71      inference('demod', [status(thm)], ['37', '38', '53', '60', '61', '62'])).
% 0.48/0.71  thf('72', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('73', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.71      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.48/0.71  thf('74', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.71      inference('demod', [status(thm)], ['33', '34'])).
% 0.48/0.71  thf('75', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.48/0.71      inference('sup+', [status(thm)], ['73', '74'])).
% 0.48/0.71  thf('76', plain,
% 0.48/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['51', '52'])).
% 0.48/0.71  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['54', '59'])).
% 0.48/0.71  thf('78', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.48/0.71  thf('79', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.48/0.71  thf('80', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.71  thf('81', plain,
% 0.48/0.71      (![X22 : $i, X23 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.48/0.71              (k5_xboole_0 @ X22 @ X23)))),
% 0.48/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.71  thf('82', plain,
% 0.48/0.71      (![X0 : $i]:
% 0.48/0.71         ((k2_xboole_0 @ X0 @ X0)
% 0.48/0.71           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['80', '81'])).
% 0.48/0.71  thf(t69_enumset1, axiom,
% 0.48/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.71  thf('83', plain,
% 0.48/0.71      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.48/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.71  thf(l51_zfmisc_1, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.71  thf('84', plain,
% 0.48/0.71      (![X64 : $i, X65 : $i]:
% 0.48/0.71         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 0.48/0.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.48/0.71  thf('85', plain,
% 0.48/0.71      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['83', '84'])).
% 0.48/0.71  thf('86', plain,
% 0.48/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.71  thf('87', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.71  thf('88', plain,
% 0.48/0.71      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['82', '85', '86', '87'])).
% 0.48/0.71  thf('89', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.48/0.71      inference('demod', [status(thm)], ['49', '50'])).
% 0.48/0.71  thf('90', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['88', '89'])).
% 0.48/0.71  thf('91', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.48/0.71      inference('sup+', [status(thm)], ['79', '90'])).
% 0.48/0.71  thf('92', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.48/0.71      inference('demod', [status(thm)], ['78', '91'])).
% 0.48/0.71  thf('93', plain,
% 0.48/0.71      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.48/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.71  thf(t70_enumset1, axiom,
% 0.48/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.48/0.71  thf('94', plain,
% 0.48/0.71      (![X37 : $i, X38 : $i]:
% 0.48/0.71         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.48/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.71  thf(d1_enumset1, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.71     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.71       ( ![E:$i]:
% 0.48/0.71         ( ( r2_hidden @ E @ D ) <=>
% 0.48/0.71           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.48/0.71  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.71  thf(zf_stmt_2, axiom,
% 0.48/0.71    (![E:$i,C:$i,B:$i,A:$i]:
% 0.48/0.71     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.48/0.71       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.48/0.71  thf(zf_stmt_3, axiom,
% 0.48/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.71     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.71       ( ![E:$i]:
% 0.48/0.71         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.48/0.71  thf('95', plain,
% 0.48/0.71      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.48/0.71         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.48/0.71          | (r2_hidden @ X29 @ X33)
% 0.48/0.71          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.71  thf('96', plain,
% 0.48/0.71      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.48/0.71         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 0.48/0.71          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 0.48/0.71      inference('simplify', [status(thm)], ['95'])).
% 0.48/0.71  thf('97', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.71         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.48/0.71          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.48/0.71      inference('sup+', [status(thm)], ['94', '96'])).
% 0.48/0.71  thf('98', plain,
% 0.48/0.71      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.48/0.71         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 0.48/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.71  thf('99', plain,
% 0.48/0.71      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.48/0.71         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 0.48/0.71      inference('simplify', [status(thm)], ['98'])).
% 0.48/0.71  thf('100', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.48/0.71      inference('sup-', [status(thm)], ['97', '99'])).
% 0.48/0.71  thf('101', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.48/0.71      inference('sup+', [status(thm)], ['93', '100'])).
% 0.48/0.71  thf('102', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.48/0.71      inference('sup+', [status(thm)], ['92', '101'])).
% 0.48/0.71  thf('103', plain,
% 0.48/0.71      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.71  thf(t4_xboole_0, axiom,
% 0.48/0.71    (![A:$i,B:$i]:
% 0.48/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.71  thf('104', plain,
% 0.48/0.71      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.48/0.71          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.48/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.71  thf('105', plain,
% 0.48/0.71      (![X0 : $i, X1 : $i]:
% 0.48/0.71         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.71      inference('sup-', [status(thm)], ['103', '104'])).
% 0.48/0.71  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.48/0.71  thf('106', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.48/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.71  thf('107', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.48/0.71      inference('demod', [status(thm)], ['105', '106'])).
% 0.48/0.71  thf('108', plain, ($false), inference('sup-', [status(thm)], ['102', '107'])).
% 0.48/0.71  
% 0.48/0.71  % SZS output end Refutation
% 0.48/0.71  
% 0.48/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
