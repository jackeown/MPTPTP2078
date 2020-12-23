%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lg2Mul26oy

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:11 EST 2020

% Result     : Theorem 42.39s
% Output     : Refutation 42.39s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 120 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  660 ( 903 expanded)
%              Number of equality atoms :   71 (  98 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t47_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t47_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('47',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['27','58'])).

thf('60',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lg2Mul26oy
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 42.39/42.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 42.39/42.62  % Solved by: fo/fo7.sh
% 42.39/42.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 42.39/42.62  % done 13128 iterations in 42.164s
% 42.39/42.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 42.39/42.62  % SZS output start Refutation
% 42.39/42.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 42.39/42.62  thf(sk_A_type, type, sk_A: $i).
% 42.39/42.62  thf(sk_B_type, type, sk_B: $i).
% 42.39/42.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 42.39/42.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 42.39/42.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 42.39/42.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 42.39/42.62  thf(t47_xboole_1, conjecture,
% 42.39/42.62    (![A:$i,B:$i]:
% 42.39/42.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 42.39/42.62  thf(zf_stmt_0, negated_conjecture,
% 42.39/42.62    (~( ![A:$i,B:$i]:
% 42.39/42.62        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 42.39/42.62          ( k4_xboole_0 @ A @ B ) ) )),
% 42.39/42.62    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 42.39/42.62  thf('0', plain,
% 42.39/42.62      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 42.39/42.62         != (k4_xboole_0 @ sk_A @ sk_B))),
% 42.39/42.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 42.39/42.62  thf(commutativity_k3_xboole_0, axiom,
% 42.39/42.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 42.39/42.62  thf('1', plain,
% 42.39/42.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.39/42.62  thf('2', plain,
% 42.39/42.62      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 42.39/42.62         != (k4_xboole_0 @ sk_A @ sk_B))),
% 42.39/42.62      inference('demod', [status(thm)], ['0', '1'])).
% 42.39/42.62  thf(commutativity_k2_xboole_0, axiom,
% 42.39/42.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 42.39/42.62  thf('3', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.39/42.62  thf(t24_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i,C:$i]:
% 42.39/42.62     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 42.39/42.62       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 42.39/42.62  thf('4', plain,
% 42.39/42.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 42.39/42.62              (k2_xboole_0 @ X14 @ X16)))),
% 42.39/42.62      inference('cnf', [status(esa)], [t24_xboole_1])).
% 42.39/42.62  thf('5', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['3', '4'])).
% 42.39/42.62  thf(t40_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i]:
% 42.39/42.62     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 42.39/42.62  thf('6', plain,
% 42.39/42.62      (![X23 : $i, X24 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 42.39/42.62           = (k4_xboole_0 @ X23 @ X24))),
% 42.39/42.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 42.39/42.62  thf(t39_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i]:
% 42.39/42.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 42.39/42.62  thf('7', plain,
% 42.39/42.62      (![X21 : $i, X22 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 42.39/42.62           = (k2_xboole_0 @ X21 @ X22))),
% 42.39/42.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 42.39/42.62  thf('8', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 42.39/42.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['6', '7'])).
% 42.39/42.62  thf(t36_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 42.39/42.62  thf('9', plain,
% 42.39/42.62      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 42.39/42.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 42.39/42.62  thf(l32_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i]:
% 42.39/42.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 42.39/42.62  thf('10', plain,
% 42.39/42.62      (![X5 : $i, X7 : $i]:
% 42.39/42.62         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 42.39/42.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 42.39/42.62  thf('11', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 42.39/42.62      inference('sup-', [status(thm)], ['9', '10'])).
% 42.39/42.62  thf(t41_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i,C:$i]:
% 42.39/42.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 42.39/42.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 42.39/42.62  thf('12', plain,
% 42.39/42.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 42.39/42.62           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 42.39/42.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 42.39/42.62  thf('13', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 42.39/42.62      inference('demod', [status(thm)], ['11', '12'])).
% 42.39/42.62  thf('14', plain,
% 42.39/42.62      (![X21 : $i, X22 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 42.39/42.62           = (k2_xboole_0 @ X21 @ X22))),
% 42.39/42.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 42.39/42.62  thf('15', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 42.39/42.62           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 42.39/42.62      inference('sup+', [status(thm)], ['13', '14'])).
% 42.39/42.62  thf('16', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.39/42.62  thf('17', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.39/42.62  thf(t1_boole, axiom,
% 42.39/42.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 42.39/42.62  thf('18', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 42.39/42.62      inference('cnf', [status(esa)], [t1_boole])).
% 42.39/42.62  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 42.39/42.62      inference('sup+', [status(thm)], ['17', '18'])).
% 42.39/42.62  thf('20', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.39/42.62  thf('21', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X1 @ X0)
% 42.39/42.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('demod', [status(thm)], ['15', '16', '19', '20'])).
% 42.39/42.62  thf('22', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 42.39/42.62           = (k2_xboole_0 @ X1 @ X0))),
% 42.39/42.62      inference('demod', [status(thm)], ['8', '21'])).
% 42.39/42.62  thf('23', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 42.39/42.62  thf('24', plain,
% 42.39/42.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 42.39/42.62              (k2_xboole_0 @ X14 @ X16)))),
% 42.39/42.62      inference('cnf', [status(esa)], [t24_xboole_1])).
% 42.39/42.62  thf('25', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['23', '24'])).
% 42.39/42.62  thf('26', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 42.39/42.62              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['22', '25'])).
% 42.39/42.62  thf('27', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 42.39/42.62           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 42.39/42.62      inference('sup+', [status(thm)], ['5', '26'])).
% 42.39/42.62  thf('28', plain,
% 42.39/42.62      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 42.39/42.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 42.39/42.62  thf(t28_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i]:
% 42.39/42.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 42.39/42.62  thf('29', plain,
% 42.39/42.62      (![X17 : $i, X18 : $i]:
% 42.39/42.62         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 42.39/42.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 42.39/42.62  thf('30', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 42.39/42.62           = (k4_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('sup-', [status(thm)], ['28', '29'])).
% 42.39/42.62  thf('31', plain,
% 42.39/42.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.39/42.62  thf('32', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 42.39/42.62           = (k4_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('demod', [status(thm)], ['30', '31'])).
% 42.39/42.62  thf(t17_xboole_1, axiom,
% 42.39/42.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 42.39/42.62  thf('33', plain,
% 42.39/42.62      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 42.39/42.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 42.39/42.62  thf('34', plain,
% 42.39/42.62      (![X5 : $i, X7 : $i]:
% 42.39/42.62         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 42.39/42.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 42.39/42.62  thf('35', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 42.39/42.62      inference('sup-', [status(thm)], ['33', '34'])).
% 42.39/42.62  thf('36', plain,
% 42.39/42.62      (![X21 : $i, X22 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 42.39/42.62           = (k2_xboole_0 @ X21 @ X22))),
% 42.39/42.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 42.39/42.62  thf('37', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 42.39/42.62           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['35', '36'])).
% 42.39/42.62  thf('38', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 42.39/42.62      inference('cnf', [status(esa)], [t1_boole])).
% 42.39/42.62  thf('39', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('demod', [status(thm)], ['37', '38'])).
% 42.39/42.62  thf('40', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['32', '39'])).
% 42.39/42.62  thf('41', plain,
% 42.39/42.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 42.39/42.62              (k2_xboole_0 @ X14 @ X16)))),
% 42.39/42.62      inference('cnf', [status(esa)], [t24_xboole_1])).
% 42.39/42.62  thf('42', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X0))),
% 42.39/42.62      inference('sup+', [status(thm)], ['40', '41'])).
% 42.39/42.62  thf('43', plain,
% 42.39/42.62      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 42.39/42.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 42.39/42.62  thf('44', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 42.39/42.62      inference('cnf', [status(esa)], [t1_boole])).
% 42.39/42.62  thf('45', plain,
% 42.39/42.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 42.39/42.62           = (k3_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ 
% 42.39/42.62              (k2_xboole_0 @ X14 @ X16)))),
% 42.39/42.62      inference('cnf', [status(esa)], [t24_xboole_1])).
% 42.39/42.62  thf('46', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 42.39/42.62           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['44', '45'])).
% 42.39/42.62  thf(idempotence_k3_xboole_0, axiom,
% 42.39/42.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 42.39/42.62  thf('47', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 42.39/42.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 42.39/42.62  thf('48', plain,
% 42.39/42.62      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 42.39/42.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 42.39/42.62  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 42.39/42.62      inference('sup+', [status(thm)], ['47', '48'])).
% 42.39/42.62  thf('50', plain,
% 42.39/42.62      (![X5 : $i, X7 : $i]:
% 42.39/42.62         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 42.39/42.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 42.39/42.62  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 42.39/42.62      inference('sup-', [status(thm)], ['49', '50'])).
% 42.39/42.62  thf('52', plain,
% 42.39/42.62      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 42.39/42.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 42.39/42.62  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 42.39/42.62      inference('sup+', [status(thm)], ['51', '52'])).
% 42.39/42.62  thf('54', plain,
% 42.39/42.62      (![X17 : $i, X18 : $i]:
% 42.39/42.62         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 42.39/42.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 42.39/42.62  thf('55', plain,
% 42.39/42.62      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 42.39/42.62      inference('sup-', [status(thm)], ['53', '54'])).
% 42.39/42.62  thf('56', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 42.39/42.62      inference('cnf', [status(esa)], [t1_boole])).
% 42.39/42.62  thf('57', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 42.39/42.62      inference('demod', [status(thm)], ['46', '55', '56'])).
% 42.39/42.62  thf('58', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 42.39/42.62           = (X0))),
% 42.39/42.62      inference('demod', [status(thm)], ['42', '43', '57'])).
% 42.39/42.62  thf('59', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 42.39/42.62           = (X1))),
% 42.39/42.62      inference('demod', [status(thm)], ['27', '58'])).
% 42.39/42.62  thf('60', plain,
% 42.39/42.62      (![X23 : $i, X24 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 42.39/42.62           = (k4_xboole_0 @ X23 @ X24))),
% 42.39/42.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 42.39/42.62  thf('61', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 42.39/42.62           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('sup+', [status(thm)], ['59', '60'])).
% 42.39/42.62  thf('62', plain,
% 42.39/42.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 42.39/42.62           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 42.39/42.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 42.39/42.62  thf('63', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 42.39/42.62      inference('demod', [status(thm)], ['37', '38'])).
% 42.39/42.62  thf('64', plain,
% 42.39/42.62      (![X0 : $i, X1 : $i]:
% 42.39/42.62         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 42.39/42.62           = (k4_xboole_0 @ X0 @ X1))),
% 42.39/42.62      inference('demod', [status(thm)], ['61', '62', '63'])).
% 42.39/42.62  thf('65', plain,
% 42.39/42.62      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 42.39/42.62      inference('demod', [status(thm)], ['2', '64'])).
% 42.39/42.62  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 42.39/42.62  
% 42.39/42.62  % SZS output end Refutation
% 42.39/42.62  
% 42.39/42.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
