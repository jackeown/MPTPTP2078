%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yMd6RBhHfv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:47 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 776 expanded)
%              Number of leaves         :   35 ( 278 expanded)
%              Depth                    :   21
%              Number of atoms          : 1089 (6588 expanded)
%              Number of equality atoms :  119 ( 731 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
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
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','26','27','28'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','40','41'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('56',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('63',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('75',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','73','76'])).

thf('78',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','73','76'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('80',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('82',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('83',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X67 @ X68 ) )
      = ( k2_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('87',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['78','88'])).

thf('90',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','89'])).

thf('91',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('92',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
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

thf('93',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X36 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('94',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('97',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X27 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','98'])).

thf('100',plain,(
    r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['90','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

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
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','110'])).

thf('112',plain,(
    $false ),
    inference('sup-',[status(thm)],['100','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yMd6RBhHfv
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:27:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.65/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.86  % Solved by: fo/fo7.sh
% 0.65/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.86  % done 882 iterations in 0.397s
% 0.65/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.86  % SZS output start Refutation
% 0.65/0.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.65/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.86  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.65/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.65/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.65/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.65/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.86  thf(t49_zfmisc_1, conjecture,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.65/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.86    (~( ![A:$i,B:$i]:
% 0.65/0.86        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.65/0.86    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.65/0.86  thf('0', plain,
% 0.65/0.86      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(commutativity_k5_xboole_0, axiom,
% 0.65/0.86    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.65/0.86  thf('1', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf(t94_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( k2_xboole_0 @ A @ B ) =
% 0.65/0.86       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.86  thf('2', plain,
% 0.65/0.86      (![X25 : $i, X26 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X25 @ X26)
% 0.65/0.86           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 0.65/0.86              (k3_xboole_0 @ X25 @ X26)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.65/0.86  thf('3', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf('4', plain,
% 0.65/0.86      (![X25 : $i, X26 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X25 @ X26)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.65/0.86              (k5_xboole_0 @ X25 @ X26)))),
% 0.65/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('5', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X0 @ X1)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['1', '4'])).
% 0.65/0.86  thf(commutativity_k3_xboole_0, axiom,
% 0.65/0.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.65/0.86  thf('6', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.86  thf('7', plain,
% 0.65/0.86      (![X25 : $i, X26 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X25 @ X26)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.65/0.86              (k5_xboole_0 @ X25 @ X26)))),
% 0.65/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('8', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X0 @ X1)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf('9', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['5', '8'])).
% 0.65/0.86  thf('10', plain,
% 0.65/0.86      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.65/0.86      inference('demod', [status(thm)], ['0', '9'])).
% 0.65/0.86  thf('11', plain,
% 0.65/0.86      (![X25 : $i, X26 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X25 @ X26)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.65/0.86              (k5_xboole_0 @ X25 @ X26)))),
% 0.65/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('12', plain,
% 0.65/0.86      (![X25 : $i, X26 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X25 @ X26)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.65/0.86              (k5_xboole_0 @ X25 @ X26)))),
% 0.65/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('13', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.65/0.86           = (k5_xboole_0 @ 
% 0.65/0.86              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.65/0.86              (k2_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['11', '12'])).
% 0.65/0.86  thf('14', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf('15', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.65/0.86           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.65/0.86              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.65/0.86      inference('demod', [status(thm)], ['13', '14'])).
% 0.65/0.86  thf('16', plain,
% 0.65/0.86      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.65/0.86         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.65/0.86            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['10', '15'])).
% 0.65/0.86  thf('17', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf(t5_boole, axiom,
% 0.65/0.86    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.86  thf('18', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.65/0.86  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['17', '18'])).
% 0.65/0.86  thf('20', plain,
% 0.65/0.86      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.65/0.86         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.65/0.86      inference('demod', [status(thm)], ['16', '19'])).
% 0.65/0.86  thf('21', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X0 @ X1)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['1', '4'])).
% 0.65/0.86  thf('22', plain,
% 0.65/0.86      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.65/0.86         = (k5_xboole_0 @ 
% 0.65/0.86            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.65/0.86            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['20', '21'])).
% 0.65/0.86  thf(t91_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.65/0.86       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.65/0.86  thf('23', plain,
% 0.65/0.86      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.65/0.86           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.86  thf('24', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.86  thf(t100_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.86  thf('25', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X10 @ X11)
% 0.65/0.86           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.86  thf('26', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X0 @ X1)
% 0.65/0.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['24', '25'])).
% 0.65/0.86  thf('27', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf('28', plain,
% 0.65/0.86      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.65/0.86           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.86  thf('29', plain,
% 0.65/0.86      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.65/0.86         = (k5_xboole_0 @ sk_B @ 
% 0.65/0.86            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.65/0.86             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.65/0.86      inference('demod', [status(thm)], ['22', '23', '26', '27', '28'])).
% 0.65/0.86  thf(t92_xboole_1, axiom,
% 0.65/0.86    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.65/0.86  thf('30', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.65/0.86  thf('31', plain,
% 0.65/0.86      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.65/0.86           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.86  thf('32', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf('33', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.65/0.86           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['31', '32'])).
% 0.65/0.86  thf('34', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.65/0.86           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['30', '33'])).
% 0.65/0.86  thf('35', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.65/0.86  thf('36', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.65/0.86      inference('demod', [status(thm)], ['34', '35'])).
% 0.65/0.86  thf('37', plain,
% 0.65/0.86      (((k5_xboole_0 @ 
% 0.65/0.86         (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.65/0.86          (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86           (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.65/0.86         (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.65/0.86          (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.65/0.86         = (sk_B))),
% 0.65/0.86      inference('sup+', [status(thm)], ['29', '36'])).
% 0.65/0.86  thf('38', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf('39', plain,
% 0.65/0.86      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.65/0.86           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.65/0.86  thf('40', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.65/0.86           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['38', '39'])).
% 0.65/0.86  thf('41', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.65/0.86      inference('demod', [status(thm)], ['34', '35'])).
% 0.65/0.86  thf('42', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.65/0.86      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.65/0.86  thf(t36_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.65/0.86  thf('43', plain,
% 0.65/0.86      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.65/0.86      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.65/0.86  thf(t28_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.65/0.86  thf('44', plain,
% 0.65/0.86      (![X14 : $i, X15 : $i]:
% 0.65/0.86         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.65/0.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.65/0.86  thf('45', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.65/0.86           = (k4_xboole_0 @ X0 @ X1))),
% 0.65/0.86      inference('sup-', [status(thm)], ['43', '44'])).
% 0.65/0.86  thf('46', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.86  thf('47', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.65/0.86           = (k4_xboole_0 @ X0 @ X1))),
% 0.65/0.86      inference('demod', [status(thm)], ['45', '46'])).
% 0.65/0.86  thf('48', plain,
% 0.65/0.86      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.65/0.86         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.65/0.86      inference('sup+', [status(thm)], ['42', '47'])).
% 0.65/0.86  thf('49', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.86  thf('50', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.65/0.86      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.65/0.86  thf('51', plain, (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.65/0.86      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.65/0.86  thf('52', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X0 @ X1)
% 0.65/0.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['24', '25'])).
% 0.65/0.86  thf('53', plain,
% 0.65/0.86      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.65/0.86         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.65/0.86      inference('sup+', [status(thm)], ['51', '52'])).
% 0.65/0.86  thf('54', plain, (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.65/0.86      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.65/0.86  thf('55', plain,
% 0.65/0.86      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.65/0.86  thf('56', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.65/0.86      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.65/0.86  thf('57', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.65/0.86  thf('58', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.65/0.86           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['31', '32'])).
% 0.65/0.86  thf('59', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.65/0.86           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['57', '58'])).
% 0.65/0.86  thf('60', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.65/0.86  thf('61', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.65/0.86      inference('demod', [status(thm)], ['59', '60'])).
% 0.65/0.86  thf('62', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.65/0.86      inference('sup+', [status(thm)], ['56', '61'])).
% 0.65/0.86  thf(t2_boole, axiom,
% 0.65/0.86    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.65/0.86  thf('63', plain,
% 0.65/0.86      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t2_boole])).
% 0.65/0.86  thf('64', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X10 @ X11)
% 0.65/0.86           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.86  thf('65', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['63', '64'])).
% 0.65/0.86  thf('66', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.65/0.86  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['65', '66'])).
% 0.65/0.86  thf('68', plain,
% 0.65/0.86      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.65/0.86      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.65/0.86  thf('69', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.65/0.86      inference('sup+', [status(thm)], ['67', '68'])).
% 0.65/0.86  thf('70', plain,
% 0.65/0.86      (![X14 : $i, X15 : $i]:
% 0.65/0.86         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.65/0.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.65/0.86  thf('71', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.65/0.86      inference('sup-', [status(thm)], ['69', '70'])).
% 0.65/0.86  thf('72', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i]:
% 0.65/0.86         ((k4_xboole_0 @ X10 @ X11)
% 0.65/0.86           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.86  thf('73', plain,
% 0.65/0.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['71', '72'])).
% 0.65/0.86  thf('74', plain,
% 0.65/0.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['71', '72'])).
% 0.65/0.86  thf('75', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.65/0.86  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['74', '75'])).
% 0.65/0.86  thf('77', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.65/0.86      inference('demod', [status(thm)], ['62', '73', '76'])).
% 0.65/0.86  thf('78', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.65/0.86      inference('demod', [status(thm)], ['62', '73', '76'])).
% 0.65/0.86  thf('79', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.65/0.86      inference('sup-', [status(thm)], ['69', '70'])).
% 0.65/0.86  thf('80', plain,
% 0.65/0.86      (![X25 : $i, X26 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X25 @ X26)
% 0.65/0.86           = (k5_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.65/0.86              (k5_xboole_0 @ X25 @ X26)))),
% 0.65/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('81', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((k2_xboole_0 @ X0 @ X0)
% 0.65/0.86           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['79', '80'])).
% 0.65/0.86  thf(t69_enumset1, axiom,
% 0.65/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.65/0.86  thf('82', plain,
% 0.65/0.86      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.65/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.86  thf(l51_zfmisc_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.65/0.86  thf('83', plain,
% 0.65/0.86      (![X67 : $i, X68 : $i]:
% 0.65/0.86         ((k3_tarski @ (k2_tarski @ X67 @ X68)) = (k2_xboole_0 @ X67 @ X68))),
% 0.65/0.86      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.65/0.86  thf('84', plain,
% 0.65/0.86      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['82', '83'])).
% 0.65/0.86  thf('85', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.65/0.86  thf('86', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((k3_tarski @ (k1_tarski @ X0)) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.86      inference('demod', [status(thm)], ['81', '84', '85'])).
% 0.65/0.86  thf('87', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.65/0.86  thf('88', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['86', '87'])).
% 0.65/0.86  thf('89', plain, (((k3_tarski @ k1_xboole_0) = (sk_A))),
% 0.65/0.86      inference('sup+', [status(thm)], ['78', '88'])).
% 0.65/0.86  thf('90', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.65/0.86      inference('demod', [status(thm)], ['77', '89'])).
% 0.65/0.86  thf('91', plain,
% 0.65/0.86      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 0.65/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.86  thf(t70_enumset1, axiom,
% 0.65/0.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.65/0.86  thf('92', plain,
% 0.65/0.86      (![X40 : $i, X41 : $i]:
% 0.65/0.86         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 0.65/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.65/0.86  thf(d1_enumset1, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.86     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.65/0.86       ( ![E:$i]:
% 0.65/0.86         ( ( r2_hidden @ E @ D ) <=>
% 0.65/0.86           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.65/0.86  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.65/0.86  thf(zf_stmt_2, axiom,
% 0.65/0.86    (![E:$i,C:$i,B:$i,A:$i]:
% 0.65/0.86     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.65/0.86       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.65/0.86  thf(zf_stmt_3, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.86     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.65/0.86       ( ![E:$i]:
% 0.65/0.86         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.65/0.86  thf('93', plain,
% 0.65/0.86      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.65/0.86         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35)
% 0.65/0.86          | (r2_hidden @ X32 @ X36)
% 0.65/0.86          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.65/0.86  thf('94', plain,
% 0.65/0.86      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.65/0.86         ((r2_hidden @ X32 @ (k1_enumset1 @ X35 @ X34 @ X33))
% 0.65/0.86          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35))),
% 0.65/0.86      inference('simplify', [status(thm)], ['93'])).
% 0.65/0.86  thf('95', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.86         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.65/0.86          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.65/0.86      inference('sup+', [status(thm)], ['92', '94'])).
% 0.65/0.86  thf('96', plain,
% 0.65/0.86      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.65/0.86         (((X28) != (X27)) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30 @ X27))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.65/0.86  thf('97', plain,
% 0.65/0.86      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.65/0.86         ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X27)),
% 0.65/0.86      inference('simplify', [status(thm)], ['96'])).
% 0.65/0.86  thf('98', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.65/0.86      inference('sup-', [status(thm)], ['95', '97'])).
% 0.65/0.86  thf('99', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['91', '98'])).
% 0.65/0.86  thf('100', plain, ((r2_hidden @ (k3_tarski @ k1_xboole_0) @ k1_xboole_0)),
% 0.65/0.86      inference('sup+', [status(thm)], ['90', '99'])).
% 0.65/0.86  thf('101', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.65/0.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.86  thf('102', plain,
% 0.65/0.86      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t2_boole])).
% 0.65/0.86  thf('103', plain,
% 0.65/0.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['101', '102'])).
% 0.65/0.86  thf(t4_xboole_0, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.86            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.86       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.65/0.86            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.65/0.86  thf('104', plain,
% 0.65/0.86      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.65/0.86          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.65/0.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.65/0.86  thf('105', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.65/0.86      inference('sup-', [status(thm)], ['103', '104'])).
% 0.65/0.86  thf('106', plain,
% 0.65/0.86      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.86      inference('cnf', [status(esa)], [t2_boole])).
% 0.65/0.86  thf(l97_xboole_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.65/0.86  thf('107', plain,
% 0.65/0.86      (![X8 : $i, X9 : $i]:
% 0.65/0.86         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.65/0.86      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.65/0.86  thf('108', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (r1_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['106', '107'])).
% 0.65/0.86  thf('109', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.65/0.86  thf('110', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.65/0.86      inference('demod', [status(thm)], ['108', '109'])).
% 0.65/0.86  thf('111', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.65/0.86      inference('demod', [status(thm)], ['105', '110'])).
% 0.65/0.86  thf('112', plain, ($false), inference('sup-', [status(thm)], ['100', '111'])).
% 0.65/0.86  
% 0.65/0.86  % SZS output end Refutation
% 0.65/0.86  
% 0.71/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
