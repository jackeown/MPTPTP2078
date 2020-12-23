%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VKRwCXehw4

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:20 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 475 expanded)
%              Number of leaves         :   21 ( 166 expanded)
%              Depth                    :   20
%              Number of atoms          :  754 (3488 expanded)
%              Number of equality atoms :   88 ( 455 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','49'])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['60','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','73','74'])).

thf('76',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VKRwCXehw4
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:36:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.90/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.11  % Solved by: fo/fo7.sh
% 0.90/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.11  % done 889 iterations in 0.665s
% 0.90/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.11  % SZS output start Refutation
% 0.90/1.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(t14_zfmisc_1, conjecture,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.90/1.11       ( k2_tarski @ A @ B ) ))).
% 0.90/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.11    (~( ![A:$i,B:$i]:
% 0.90/1.11        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.90/1.11          ( k2_tarski @ A @ B ) ) )),
% 0.90/1.11    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.90/1.11  thf('0', plain,
% 0.90/1.11      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.90/1.11         != (k2_tarski @ sk_A @ sk_B))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(t12_zfmisc_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.90/1.11  thf('1', plain,
% 0.90/1.11      (![X47 : $i, X48 : $i]:
% 0.90/1.11         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X47 @ X48))),
% 0.90/1.11      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.90/1.11  thf(t28_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.11  thf('2', plain,
% 0.90/1.11      (![X10 : $i, X11 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.90/1.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.11  thf('3', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.90/1.11           = (k1_tarski @ X1))),
% 0.90/1.11      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.11  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.11  thf('4', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.11  thf(t100_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.11  thf('5', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X7 @ X8)
% 0.90/1.11           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.11  thf('6', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.11  thf('7', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 0.90/1.11           = (k5_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['3', '6'])).
% 0.90/1.11  thf(commutativity_k5_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.90/1.11  thf('8', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('9', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))
% 0.90/1.11           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['7', '8'])).
% 0.90/1.11  thf(d10_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.11  thf('10', plain,
% 0.90/1.11      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.90/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.11  thf('11', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.90/1.11      inference('simplify', [status(thm)], ['10'])).
% 0.90/1.11  thf('12', plain,
% 0.90/1.11      (![X10 : $i, X11 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.90/1.11      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.90/1.11  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['11', '12'])).
% 0.90/1.11  thf('14', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X7 @ X8)
% 0.90/1.11           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.11  thf('15', plain,
% 0.90/1.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['13', '14'])).
% 0.90/1.11  thf(t1_boole, axiom,
% 0.90/1.11    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.11  thf('16', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [t1_boole])).
% 0.90/1.11  thf(t46_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.90/1.11  thf('17', plain,
% 0.90/1.11      (![X12 : $i, X13 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.90/1.11  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['16', '17'])).
% 0.90/1.11  thf('19', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '18'])).
% 0.90/1.11  thf(t91_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.11       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.90/1.11  thf('20', plain,
% 0.90/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.90/1.11           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.11  thf('21', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('22', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.90/1.11           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['20', '21'])).
% 0.90/1.11  thf('23', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['19', '22'])).
% 0.90/1.11  thf('24', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X7 @ X8)
% 0.90/1.11           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.11  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['16', '17'])).
% 0.90/1.11  thf(t98_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.90/1.11  thf('26', plain,
% 0.90/1.11      (![X17 : $i, X18 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X17 @ X18)
% 0.90/1.11           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.11  thf('27', plain,
% 0.90/1.11      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['25', '26'])).
% 0.90/1.11  thf('28', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('29', plain,
% 0.90/1.11      (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['27', '28'])).
% 0.90/1.11  thf('30', plain,
% 0.90/1.11      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['25', '26'])).
% 0.90/1.11  thf('31', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['15', '18'])).
% 0.90/1.11  thf('32', plain,
% 0.90/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.90/1.11           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.11  thf('33', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['31', '32'])).
% 0.90/1.11  thf('34', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['30', '33'])).
% 0.90/1.11  thf('35', plain,
% 0.90/1.11      (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['27', '28'])).
% 0.90/1.11  thf('36', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [t1_boole])).
% 0.90/1.11  thf('37', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.11  thf('38', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['29', '37'])).
% 0.90/1.11  thf('39', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.90/1.11              (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['24', '38'])).
% 0.90/1.11  thf('40', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('41', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.90/1.11              (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['39', '40'])).
% 0.90/1.11  thf('42', plain,
% 0.90/1.11      (![X17 : $i, X18 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X17 @ X18)
% 0.90/1.11           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.11  thf('43', plain,
% 0.90/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.90/1.11           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.11  thf('44', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.90/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['42', '43'])).
% 0.90/1.11  thf('45', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.90/1.11           (k3_xboole_0 @ k1_xboole_0 @ X0)) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['41', '44'])).
% 0.90/1.11  thf('46', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [t1_boole])).
% 0.90/1.11  thf('47', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.11  thf('48', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.90/1.11  thf('49', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['23', '48'])).
% 0.90/1.11  thf('50', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 0.90/1.11              (k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))))),
% 0.90/1.11      inference('sup+', [status(thm)], ['9', '49'])).
% 0.90/1.11  thf('51', plain,
% 0.90/1.11      (![X17 : $i, X18 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X17 @ X18)
% 0.90/1.11           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.11  thf('52', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k2_tarski @ X0 @ X1) @ k1_xboole_0)
% 0.90/1.11           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1)))),
% 0.90/1.11      inference('demod', [status(thm)], ['50', '51'])).
% 0.90/1.11  thf('53', plain,
% 0.90/1.11      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)
% 0.90/1.11         != (k2_tarski @ sk_A @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['0', '52'])).
% 0.90/1.11  thf('54', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.90/1.11  thf('55', plain,
% 0.90/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.90/1.11           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.11  thf('56', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['54', '55'])).
% 0.90/1.11  thf('57', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.90/1.11  thf('58', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('59', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['57', '58'])).
% 0.90/1.11  thf('60', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['56', '59'])).
% 0.90/1.11  thf('61', plain,
% 0.90/1.11      (![X7 : $i, X8 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X7 @ X8)
% 0.90/1.11           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.11  thf('62', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('63', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['31', '32'])).
% 0.90/1.11  thf('64', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['62', '63'])).
% 0.90/1.11  thf('65', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['61', '64'])).
% 0.90/1.11  thf('66', plain,
% 0.90/1.11      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.90/1.11      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.11  thf('67', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['65', '66'])).
% 0.90/1.11  thf('68', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['57', '58'])).
% 0.90/1.11  thf('69', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['67', '68'])).
% 0.90/1.11  thf('70', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ 
% 0.90/1.11              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['60', '69'])).
% 0.90/1.11  thf('71', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['57', '58'])).
% 0.90/1.11  thf('72', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ X1)
% 0.90/1.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.11  thf('73', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.11           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['71', '72'])).
% 0.90/1.11  thf('74', plain,
% 0.90/1.11      (![X17 : $i, X18 : $i]:
% 0.90/1.11         ((k2_xboole_0 @ X17 @ X18)
% 0.90/1.11           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.90/1.11  thf('75', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['70', '73', '74'])).
% 0.90/1.11  thf('76', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.90/1.11      inference('cnf', [status(esa)], [t1_boole])).
% 0.90/1.11  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['75', '76'])).
% 0.90/1.11  thf('78', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.90/1.11      inference('demod', [status(thm)], ['53', '77'])).
% 0.90/1.11  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
