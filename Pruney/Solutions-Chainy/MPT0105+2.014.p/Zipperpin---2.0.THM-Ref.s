%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d2kR5QBp6r

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:06 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 926 expanded)
%              Number of leaves         :   22 ( 323 expanded)
%              Depth                    :   26
%              Number of atoms          : 1072 (7160 expanded)
%              Number of equality atoms :  128 ( 903 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','43'])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ X5 @ X6 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','57'])).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','25'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('91',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('95',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('106',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('107',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','108'])).

thf('110',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','107'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','114'])).

thf('116',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','115'])).

thf('117',plain,(
    $false ),
    inference(simplify,[status(thm)],['116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d2kR5QBp6r
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.02/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.23  % Solved by: fo/fo7.sh
% 1.02/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.23  % done 1496 iterations in 0.775s
% 1.02/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.23  % SZS output start Refutation
% 1.02/1.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.23  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.02/1.23  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.23  thf(t98_xboole_1, conjecture,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.02/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.23    (~( ![A:$i,B:$i]:
% 1.02/1.23        ( ( k2_xboole_0 @ A @ B ) =
% 1.02/1.23          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 1.02/1.23    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 1.02/1.23  thf('0', plain,
% 1.02/1.23      (((k2_xboole_0 @ sk_A @ sk_B)
% 1.02/1.23         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 1.02/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.23  thf(commutativity_k3_xboole_0, axiom,
% 1.02/1.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.02/1.23  thf('1', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.23  thf(t94_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k2_xboole_0 @ A @ B ) =
% 1.02/1.23       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.02/1.23  thf('2', plain,
% 1.02/1.23      (![X26 : $i, X27 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ X26 @ X27)
% 1.02/1.23           = (k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ 
% 1.02/1.23              (k3_xboole_0 @ X26 @ X27)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.02/1.23  thf(t91_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i,C:$i]:
% 1.02/1.23     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.02/1.23       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.02/1.23  thf('3', plain,
% 1.02/1.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.02/1.23           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.02/1.23  thf('4', plain,
% 1.02/1.23      (![X26 : $i, X27 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ X26 @ X27)
% 1.02/1.23           = (k5_xboole_0 @ X26 @ 
% 1.02/1.23              (k5_xboole_0 @ X27 @ (k3_xboole_0 @ X26 @ X27))))),
% 1.02/1.23      inference('demod', [status(thm)], ['2', '3'])).
% 1.02/1.23  thf('5', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ X0 @ X1)
% 1.02/1.23           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.02/1.23      inference('sup+', [status(thm)], ['1', '4'])).
% 1.02/1.23  thf(t48_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.02/1.23  thf('6', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf(t41_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i,C:$i]:
% 1.02/1.23     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.02/1.23       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.02/1.23  thf('7', plain,
% 1.02/1.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.02/1.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.23  thf(t3_boole, axiom,
% 1.02/1.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.23  thf('8', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.02/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.23  thf('9', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('10', plain,
% 1.02/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['8', '9'])).
% 1.02/1.23  thf('11', plain,
% 1.02/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['8', '9'])).
% 1.02/1.23  thf('12', plain,
% 1.02/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['8', '9'])).
% 1.02/1.23  thf(t49_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i,C:$i]:
% 1.02/1.23     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.02/1.23       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.02/1.23  thf('13', plain,
% 1.02/1.23      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 1.02/1.23           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 1.02/1.23      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.02/1.23  thf('14', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 1.02/1.23           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 1.02/1.23      inference('sup+', [status(thm)], ['12', '13'])).
% 1.02/1.23  thf('15', plain,
% 1.02/1.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.02/1.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.23  thf(t46_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.02/1.23  thf('16', plain,
% 1.02/1.23      (![X13 : $i, X14 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 1.02/1.23      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.02/1.23  thf('17', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1)) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.02/1.23  thf('18', plain,
% 1.02/1.23      (![X0 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 1.02/1.23           = (k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['11', '17'])).
% 1.02/1.23  thf('19', plain,
% 1.02/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['8', '9'])).
% 1.02/1.23  thf(t47_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.02/1.23  thf('20', plain,
% 1.02/1.23      (![X15 : $i, X16 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 1.02/1.23           = (k4_xboole_0 @ X15 @ X16))),
% 1.02/1.23      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.02/1.23  thf('21', plain,
% 1.02/1.23      (![X0 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 1.02/1.23           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['19', '20'])).
% 1.02/1.23  thf('22', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('23', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.02/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.23  thf('24', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.02/1.23  thf('25', plain,
% 1.02/1.23      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['18', '24'])).
% 1.02/1.23  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['10', '25'])).
% 1.02/1.23  thf('27', plain,
% 1.02/1.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.02/1.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.23  thf('28', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k1_xboole_0)
% 1.02/1.23           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.02/1.23      inference('sup+', [status(thm)], ['26', '27'])).
% 1.02/1.23  thf('29', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('30', plain,
% 1.02/1.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.02/1.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.23  thf('31', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.02/1.23           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['29', '30'])).
% 1.02/1.23  thf('32', plain,
% 1.02/1.23      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 1.02/1.23           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 1.02/1.23      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.02/1.23  thf('33', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 1.02/1.23           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.02/1.23      inference('demod', [status(thm)], ['31', '32'])).
% 1.02/1.23  thf('34', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X1 @ 
% 1.02/1.23           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))
% 1.02/1.23           = (k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['28', '33'])).
% 1.02/1.23  thf('35', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('36', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.23  thf('37', plain,
% 1.02/1.23      (![X15 : $i, X16 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 1.02/1.23           = (k4_xboole_0 @ X15 @ X16))),
% 1.02/1.23      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.02/1.23  thf('38', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.23      inference('sup+', [status(thm)], ['36', '37'])).
% 1.02/1.23  thf('39', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['34', '35', '38'])).
% 1.02/1.23  thf('40', plain,
% 1.02/1.23      (![X15 : $i, X16 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 1.02/1.23           = (k4_xboole_0 @ X15 @ X16))),
% 1.02/1.23      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.02/1.23  thf('41', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.02/1.23           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['39', '40'])).
% 1.02/1.23  thf('42', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.02/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.23  thf('43', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('demod', [status(thm)], ['41', '42'])).
% 1.02/1.23  thf('44', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         ((X0)
% 1.02/1.23           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.02/1.23      inference('sup+', [status(thm)], ['7', '43'])).
% 1.02/1.23  thf('45', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('46', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['44', '45'])).
% 1.02/1.23  thf('47', plain,
% 1.02/1.23      (![X15 : $i, X16 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 1.02/1.23           = (k4_xboole_0 @ X15 @ X16))),
% 1.02/1.23      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.02/1.23  thf('48', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ X0)
% 1.02/1.23           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['46', '47'])).
% 1.02/1.23  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['10', '25'])).
% 1.02/1.23  thf('50', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('demod', [status(thm)], ['48', '49'])).
% 1.02/1.23  thf('51', plain,
% 1.02/1.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 1.02/1.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.02/1.23  thf(l32_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.23  thf('52', plain,
% 1.02/1.23      (![X2 : $i, X3 : $i]:
% 1.02/1.23         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 1.02/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.23  thf('53', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.02/1.23          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['51', '52'])).
% 1.02/1.23  thf('54', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         (((k1_xboole_0) != (k1_xboole_0))
% 1.02/1.23          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['50', '53'])).
% 1.02/1.23  thf('55', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.02/1.23      inference('simplify', [status(thm)], ['54'])).
% 1.02/1.23  thf(t12_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.02/1.23  thf('56', plain,
% 1.02/1.23      (![X7 : $i, X8 : $i]:
% 1.02/1.23         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 1.02/1.23      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.23  thf('57', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['55', '56'])).
% 1.02/1.23  thf('58', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.02/1.23      inference('sup+', [status(thm)], ['6', '57'])).
% 1.02/1.23  thf('59', plain,
% 1.02/1.23      (![X13 : $i, X14 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 1.02/1.23      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.02/1.23  thf('60', plain,
% 1.02/1.23      (![X2 : $i, X3 : $i]:
% 1.02/1.23         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 1.02/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.23  thf('61', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         (((k1_xboole_0) != (k1_xboole_0))
% 1.02/1.23          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup-', [status(thm)], ['59', '60'])).
% 1.02/1.23  thf('62', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.02/1.23      inference('simplify', [status(thm)], ['61'])).
% 1.02/1.23  thf('63', plain,
% 1.02/1.23      (![X7 : $i, X8 : $i]:
% 1.02/1.23         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 1.02/1.23      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.23  thf('64', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k2_xboole_0 @ X1 @ X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['62', '63'])).
% 1.02/1.23  thf(l98_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k5_xboole_0 @ A @ B ) =
% 1.02/1.23       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.02/1.23  thf('65', plain,
% 1.02/1.23      (![X5 : $i, X6 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X5 @ X6)
% 1.02/1.23           = (k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X6)))),
% 1.02/1.23      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.02/1.23  thf('66', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.02/1.23              (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.02/1.23      inference('sup+', [status(thm)], ['64', '65'])).
% 1.02/1.23  thf('67', plain,
% 1.02/1.23      (![X13 : $i, X14 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 1.02/1.23      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.02/1.23  thf('68', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('69', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 1.02/1.23           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['67', '68'])).
% 1.02/1.23  thf('70', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.02/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.23  thf('71', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('demod', [status(thm)], ['69', '70'])).
% 1.02/1.23  thf('72', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.02/1.23      inference('demod', [status(thm)], ['66', '71'])).
% 1.02/1.23  thf('73', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 1.02/1.23           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))
% 1.02/1.23           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['58', '72'])).
% 1.02/1.23  thf('74', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.02/1.23      inference('sup+', [status(thm)], ['6', '57'])).
% 1.02/1.23  thf('75', plain,
% 1.02/1.23      (![X15 : $i, X16 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 1.02/1.23           = (k4_xboole_0 @ X15 @ X16))),
% 1.02/1.23      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.02/1.23  thf('76', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.02/1.23           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.23      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.02/1.23  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['10', '25'])).
% 1.02/1.23  thf('78', plain,
% 1.02/1.23      (![X2 : $i, X3 : $i]:
% 1.02/1.23         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 1.02/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.23  thf('79', plain,
% 1.02/1.23      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['77', '78'])).
% 1.02/1.23  thf('80', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.02/1.23      inference('simplify', [status(thm)], ['79'])).
% 1.02/1.23  thf('81', plain,
% 1.02/1.23      (![X7 : $i, X8 : $i]:
% 1.02/1.23         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 1.02/1.23      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.23  thf('82', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['80', '81'])).
% 1.02/1.23  thf('83', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.02/1.23      inference('demod', [status(thm)], ['66', '71'])).
% 1.02/1.23  thf('84', plain,
% 1.02/1.23      (![X0 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))
% 1.02/1.23           = (k4_xboole_0 @ X0 @ X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['82', '83'])).
% 1.02/1.23  thf('85', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['80', '81'])).
% 1.02/1.23  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['10', '25'])).
% 1.02/1.23  thf('87', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.02/1.23  thf('88', plain,
% 1.02/1.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.02/1.23           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.02/1.23  thf('89', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k1_xboole_0)
% 1.02/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.02/1.23      inference('sup+', [status(thm)], ['87', '88'])).
% 1.02/1.23  thf('90', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.02/1.23  thf('91', plain,
% 1.02/1.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 1.02/1.23           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.02/1.23  thf('92', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.02/1.23           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['90', '91'])).
% 1.02/1.23  thf('93', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1)) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.02/1.23  thf('94', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.02/1.23  thf('95', plain,
% 1.02/1.23      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['93', '94'])).
% 1.02/1.23  thf('96', plain,
% 1.02/1.23      (![X17 : $i, X18 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.02/1.23           = (k3_xboole_0 @ X17 @ X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('97', plain,
% 1.02/1.23      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['95', '96'])).
% 1.02/1.23  thf('98', plain,
% 1.02/1.23      (![X26 : $i, X27 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ X26 @ X27)
% 1.02/1.23           = (k5_xboole_0 @ X26 @ 
% 1.02/1.23              (k5_xboole_0 @ X27 @ (k3_xboole_0 @ X26 @ X27))))),
% 1.02/1.23      inference('demod', [status(thm)], ['2', '3'])).
% 1.02/1.23  thf('99', plain,
% 1.02/1.23      (![X0 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.02/1.23           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['97', '98'])).
% 1.02/1.23  thf('100', plain,
% 1.02/1.23      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['93', '94'])).
% 1.02/1.23  thf('101', plain,
% 1.02/1.23      (![X2 : $i, X3 : $i]:
% 1.02/1.23         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 1.02/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.23  thf('102', plain,
% 1.02/1.23      (![X0 : $i]:
% 1.02/1.23         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['100', '101'])).
% 1.02/1.23  thf('103', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.02/1.23      inference('simplify', [status(thm)], ['102'])).
% 1.02/1.23  thf('104', plain,
% 1.02/1.23      (![X7 : $i, X8 : $i]:
% 1.02/1.23         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 1.02/1.23      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.02/1.23  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['103', '104'])).
% 1.02/1.23  thf(t5_boole, axiom,
% 1.02/1.23    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.23  thf('106', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.02/1.23      inference('cnf', [status(esa)], [t5_boole])).
% 1.02/1.23  thf('107', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.02/1.23      inference('demod', [status(thm)], ['99', '105', '106'])).
% 1.02/1.23  thf('108', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('demod', [status(thm)], ['92', '107'])).
% 1.02/1.23  thf('109', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['89', '108'])).
% 1.02/1.23  thf('110', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.02/1.23      inference('cnf', [status(esa)], [t5_boole])).
% 1.02/1.23  thf('111', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.02/1.23      inference('demod', [status(thm)], ['109', '110'])).
% 1.02/1.23  thf('112', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('demod', [status(thm)], ['92', '107'])).
% 1.02/1.23  thf('113', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['111', '112'])).
% 1.02/1.23  thf('114', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.02/1.23           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.23      inference('demod', [status(thm)], ['76', '113'])).
% 1.02/1.23  thf('115', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k2_xboole_0 @ X0 @ X1)
% 1.02/1.23           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('demod', [status(thm)], ['5', '114'])).
% 1.02/1.23  thf('116', plain,
% 1.02/1.23      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 1.02/1.23      inference('demod', [status(thm)], ['0', '115'])).
% 1.02/1.23  thf('117', plain, ($false), inference('simplify', [status(thm)], ['116'])).
% 1.02/1.23  
% 1.02/1.23  % SZS output end Refutation
% 1.02/1.23  
% 1.08/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
