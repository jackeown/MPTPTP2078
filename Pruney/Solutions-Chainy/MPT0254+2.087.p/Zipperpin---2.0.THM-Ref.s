%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGmt1demA1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:47 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  134 (1300 expanded)
%              Number of leaves         :   28 ( 450 expanded)
%              Depth                    :   29
%              Number of atoms          : 1241 (11577 expanded)
%              Number of equality atoms :  113 (1275 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
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
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
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

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('46',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('50',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('55',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','50','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('57',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('66',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('68',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('70',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('76',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('84',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('86',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_B ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('91',plain,(
    ! [X0: $i] :
      ( sk_B
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['75','91'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('93',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('94',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('96',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['94','96'])).

thf('98',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('99',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X21 @ X22 @ X19 ) ),
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
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['92','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('104',plain,(
    $false ),
    inference('sup-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGmt1demA1
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 494 iterations in 0.341s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.58/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.80  thf(t49_zfmisc_1, conjecture,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i,B:$i]:
% 0.58/0.80        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.58/0.80  thf('0', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(commutativity_k5_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf(t94_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( k2_xboole_0 @ A @ B ) =
% 0.58/0.80       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (![X17 : $i, X18 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X17 @ X18)
% 0.58/0.80           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.58/0.80              (k3_xboole_0 @ X17 @ X18)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X17 : $i, X18 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X17 @ X18)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 0.58/0.80              (k5_xboole_0 @ X17 @ X18)))),
% 0.58/0.80      inference('demod', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['1', '4'])).
% 0.58/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      (![X17 : $i, X18 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X17 @ X18)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 0.58/0.80              (k5_xboole_0 @ X17 @ X18)))),
% 0.58/0.80      inference('demod', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['5', '8'])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['0', '9'])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (![X17 : $i, X18 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X17 @ X18)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 0.58/0.80              (k5_xboole_0 @ X17 @ X18)))),
% 0.58/0.80      inference('demod', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X17 : $i, X18 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X17 @ X18)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 0.58/0.80              (k5_xboole_0 @ X17 @ X18)))),
% 0.58/0.80      inference('demod', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.58/0.80           = (k5_xboole_0 @ 
% 0.58/0.80              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.58/0.80              (k2_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.58/0.80           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.58/0.80              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.58/0.80      inference('demod', [status(thm)], ['13', '14'])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.58/0.80            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('sup+', [status(thm)], ['10', '15'])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf(t5_boole, axiom,
% 0.58/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.80  thf('18', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.58/0.80      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.80  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.58/0.80      inference('demod', [status(thm)], ['16', '19'])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['1', '4'])).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k5_xboole_0 @ 
% 0.58/0.80            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.58/0.80            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('sup+', [status(thm)], ['20', '21'])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf(t91_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.80       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.58/0.80           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf(t100_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (![X10 : $i, X11 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.80           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.58/0.80             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.58/0.80      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.58/0.80      inference('demod', [status(thm)], ['16', '19'])).
% 0.58/0.80  thf('31', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.80  thf('32', plain,
% 0.58/0.80      (![X10 : $i, X11 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.80           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.80  thf('33', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.58/0.80  thf('34', plain,
% 0.58/0.80      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('sup+', [status(thm)], ['30', '33'])).
% 0.58/0.80  thf('35', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('36', plain,
% 0.58/0.80      (((k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.58/0.80            (k5_xboole_0 @ sk_B @ 
% 0.58/0.80             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.58/0.80      inference('demod', [status(thm)], ['34', '35'])).
% 0.58/0.80  thf('37', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf(t92_xboole_1, axiom,
% 0.58/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.58/0.80  thf('38', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.58/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.58/0.80  thf('39', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.58/0.80           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.80  thf('40', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.58/0.80           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['38', '39'])).
% 0.58/0.80  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.80  thf('42', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.58/0.80  thf('43', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['37', '42'])).
% 0.58/0.80  thf('44', plain,
% 0.58/0.80      (((k1_tarski @ sk_A)
% 0.58/0.80         = (k5_xboole_0 @ 
% 0.58/0.80            (k5_xboole_0 @ sk_B @ 
% 0.58/0.80             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.58/0.80            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('sup+', [status(thm)], ['36', '43'])).
% 0.58/0.80  thf('45', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('46', plain,
% 0.58/0.80      (((k1_tarski @ sk_A)
% 0.58/0.80         = (k5_xboole_0 @ 
% 0.58/0.80            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.58/0.80            (k5_xboole_0 @ sk_B @ 
% 0.58/0.80             (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80              (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.58/0.80      inference('demod', [status(thm)], ['44', '45'])).
% 0.58/0.80  thf('47', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.58/0.80  thf('48', plain,
% 0.58/0.80      (((k5_xboole_0 @ sk_B @ 
% 0.58/0.80         (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80          (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.58/0.80         = (k5_xboole_0 @ 
% 0.58/0.80            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.58/0.80            (k1_tarski @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['46', '47'])).
% 0.58/0.80  thf('49', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('50', plain,
% 0.58/0.80      (((k5_xboole_0 @ sk_B @ 
% 0.58/0.80         (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80          (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.58/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.58/0.80            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('demod', [status(thm)], ['48', '49'])).
% 0.58/0.80  thf('51', plain,
% 0.58/0.80      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.58/0.80           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.80  thf('52', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('53', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.58/0.80           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.80  thf('54', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('55', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k5_xboole_0 @ sk_B @ 
% 0.58/0.80            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80              (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.58/0.80      inference('demod', [status(thm)], ['29', '50', '53', '54'])).
% 0.58/0.80  thf('56', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['37', '42'])).
% 0.58/0.80  thf('57', plain,
% 0.58/0.80      (((sk_B)
% 0.58/0.80         = (k5_xboole_0 @ 
% 0.58/0.80            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80              (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.58/0.80            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('sup+', [status(thm)], ['55', '56'])).
% 0.58/0.80  thf('58', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.58/0.80  thf('59', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.58/0.80           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.80  thf('60', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.58/0.80      inference('demod', [status(thm)], ['16', '19'])).
% 0.58/0.80  thf('61', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.58/0.80  thf('62', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['37', '42'])).
% 0.58/0.80  thf('63', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X1)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['61', '62'])).
% 0.58/0.80  thf('64', plain,
% 0.58/0.80      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.58/0.80         = (k5_xboole_0 @ 
% 0.58/0.80            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.58/0.80            (k4_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('sup+', [status(thm)], ['60', '63'])).
% 0.58/0.80  thf('65', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.58/0.80           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.80  thf('66', plain,
% 0.58/0.80      (((sk_B)
% 0.58/0.80         = (k5_xboole_0 @ sk_B @ 
% 0.58/0.80            (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.58/0.80             (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.58/0.80      inference('demod', [status(thm)], ['57', '58', '59', '64', '65'])).
% 0.58/0.80  thf('67', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.58/0.80  thf('68', plain,
% 0.58/0.80      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.58/0.80         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.80         = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.58/0.80      inference('sup+', [status(thm)], ['66', '67'])).
% 0.58/0.80  thf('69', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.58/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.58/0.80  thf('70', plain,
% 0.58/0.80      (((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.58/0.80         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) = (k1_xboole_0))),
% 0.58/0.80      inference('demod', [status(thm)], ['68', '69'])).
% 0.58/0.80  thf('71', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.58/0.80  thf('72', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.58/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['70', '71'])).
% 0.58/0.80  thf('73', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.80  thf('75', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.58/0.80  thf(d5_xboole_0, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.58/0.80       ( ![D:$i]:
% 0.58/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.80           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.58/0.80  thf('76', plain,
% 0.58/0.80      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.58/0.80         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.58/0.80          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.58/0.80          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.58/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.80  thf('77', plain,
% 0.58/0.80      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.58/0.80  thf('78', plain,
% 0.58/0.80      (![X10 : $i, X11 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X10 @ X11)
% 0.58/0.80           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.80  thf('79', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['37', '42'])).
% 0.58/0.80  thf('80', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((X1)
% 0.58/0.80           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['78', '79'])).
% 0.58/0.80  thf('81', plain,
% 0.58/0.80      (((sk_B)
% 0.58/0.80         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.58/0.80            (k1_tarski @ sk_A)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['77', '80'])).
% 0.58/0.80  thf('82', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.80      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.80  thf('83', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k4_xboole_0 @ X0 @ X1)
% 0.58/0.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.58/0.80  thf('84', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.58/0.80      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.58/0.80  thf('85', plain,
% 0.58/0.80      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X8 @ X7)
% 0.58/0.80          | ~ (r2_hidden @ X8 @ X6)
% 0.58/0.80          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.58/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.58/0.80  thf('86', plain,
% 0.58/0.80      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X8 @ X6)
% 0.58/0.80          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['85'])).
% 0.58/0.80  thf('87', plain,
% 0.58/0.80      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['84', '86'])).
% 0.58/0.80  thf('88', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.58/0.80      inference('simplify', [status(thm)], ['87'])).
% 0.58/0.80  thf('89', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((r2_hidden @ (sk_D @ X1 @ X0 @ sk_B) @ X1)
% 0.58/0.80          | ((X1) = (k4_xboole_0 @ sk_B @ X0)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['76', '88'])).
% 0.58/0.80  thf('90', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.58/0.80      inference('simplify', [status(thm)], ['87'])).
% 0.58/0.80  thf('91', plain, (![X0 : $i]: ((sk_B) = (k4_xboole_0 @ sk_B @ X0))),
% 0.58/0.80      inference('sup-', [status(thm)], ['89', '90'])).
% 0.58/0.80  thf('92', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.58/0.80      inference('demod', [status(thm)], ['75', '91'])).
% 0.58/0.80  thf(t69_enumset1, axiom,
% 0.58/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.80  thf('93', plain,
% 0.58/0.80      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.58/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.80  thf(t70_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.80  thf('94', plain,
% 0.58/0.80      (![X32 : $i, X33 : $i]:
% 0.58/0.80         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.58/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.80  thf(d1_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.80       ( ![E:$i]:
% 0.58/0.80         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.80           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.80  thf(zf_stmt_2, axiom,
% 0.58/0.80    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.80     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.80       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_3, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.80       ( ![E:$i]:
% 0.58/0.80         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.80  thf('95', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.58/0.80          | (r2_hidden @ X24 @ X28)
% 0.58/0.80          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.80  thf('96', plain,
% 0.58/0.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.80         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 0.58/0.80          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 0.58/0.80      inference('simplify', [status(thm)], ['95'])).
% 0.58/0.80  thf('97', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.80          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.58/0.80      inference('sup+', [status(thm)], ['94', '96'])).
% 0.58/0.80  thf('98', plain,
% 0.58/0.80      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.58/0.80         (((X20) != (X19)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.80  thf('99', plain,
% 0.58/0.80      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.58/0.80         ~ (zip_tseitin_0 @ X19 @ X21 @ X22 @ X19)),
% 0.58/0.80      inference('simplify', [status(thm)], ['98'])).
% 0.58/0.80  thf('100', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['97', '99'])).
% 0.58/0.80  thf('101', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['93', '100'])).
% 0.58/0.80  thf('102', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.58/0.80      inference('sup+', [status(thm)], ['92', '101'])).
% 0.58/0.80  thf('103', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.58/0.80      inference('simplify', [status(thm)], ['87'])).
% 0.58/0.80  thf('104', plain, ($false), inference('sup-', [status(thm)], ['102', '103'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
