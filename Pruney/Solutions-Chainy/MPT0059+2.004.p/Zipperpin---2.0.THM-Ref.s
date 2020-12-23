%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WjaZWPy4wB

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:20 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 305 expanded)
%              Number of leaves         :   17 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          :  655 (2197 expanded)
%              Number of equality atoms :   68 ( 237 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t52_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['25','28','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['25','28','45'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['25','28','45'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','51','61'])).

thf('63',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WjaZWPy4wB
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:18:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.27/1.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.27/1.52  % Solved by: fo/fo7.sh
% 1.27/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.52  % done 1778 iterations in 1.104s
% 1.27/1.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.27/1.52  % SZS output start Refutation
% 1.27/1.52  thf(sk_C_type, type, sk_C: $i).
% 1.27/1.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.27/1.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.27/1.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.27/1.52  thf(t52_xboole_1, conjecture,
% 1.27/1.52    (![A:$i,B:$i,C:$i]:
% 1.27/1.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.27/1.52       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.27/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.52    (~( ![A:$i,B:$i,C:$i]:
% 1.27/1.52        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.27/1.52          ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )),
% 1.27/1.52    inference('cnf.neg', [status(esa)], [t52_xboole_1])).
% 1.27/1.52  thf('0', plain,
% 1.27/1.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.27/1.52         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 1.27/1.52             (k3_xboole_0 @ sk_A @ sk_C)))),
% 1.27/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.52  thf(commutativity_k3_xboole_0, axiom,
% 1.27/1.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.27/1.52  thf('1', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.52  thf(t48_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i]:
% 1.27/1.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.27/1.52  thf('2', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf(l36_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i,C:$i]:
% 1.27/1.52     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 1.27/1.52       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.27/1.52  thf('3', plain,
% 1.27/1.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 1.27/1.52           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X2 @ X4)))),
% 1.27/1.52      inference('cnf', [status(esa)], [l36_xboole_1])).
% 1.27/1.52  thf('4', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.27/1.52           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['2', '3'])).
% 1.27/1.52  thf('5', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 1.27/1.52           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X2 @ X1)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['1', '4'])).
% 1.27/1.52  thf(t3_boole, axiom,
% 1.27/1.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.27/1.52  thf('6', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.27/1.52      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.52  thf(t36_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.27/1.52  thf('7', plain,
% 1.27/1.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.27/1.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.27/1.52  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.27/1.52      inference('sup+', [status(thm)], ['6', '7'])).
% 1.27/1.52  thf(t37_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i]:
% 1.27/1.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.27/1.52  thf('9', plain,
% 1.27/1.52      (![X10 : $i, X12 : $i]:
% 1.27/1.52         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 1.27/1.52          | ~ (r1_tarski @ X10 @ X12))),
% 1.27/1.52      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.27/1.52  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['8', '9'])).
% 1.27/1.52  thf('11', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf('12', plain,
% 1.27/1.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.27/1.52      inference('sup+', [status(thm)], ['10', '11'])).
% 1.27/1.52  thf('13', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.27/1.52      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.52  thf('14', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.27/1.52      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.52  thf(t16_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i,C:$i]:
% 1.27/1.52     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.27/1.52       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.27/1.52  thf('15', plain,
% 1.27/1.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 1.27/1.52           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.27/1.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.27/1.52  thf('16', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.52  thf('17', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.27/1.52           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['15', '16'])).
% 1.27/1.52  thf('18', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X1 @ X0)
% 1.27/1.52           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['14', '17'])).
% 1.27/1.52  thf('19', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf('20', plain,
% 1.27/1.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.27/1.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.27/1.52  thf('21', plain,
% 1.27/1.52      (![X10 : $i, X12 : $i]:
% 1.27/1.52         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 1.27/1.52          | ~ (r1_tarski @ X10 @ X12))),
% 1.27/1.52      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.27/1.52  thf('22', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['20', '21'])).
% 1.27/1.52  thf('23', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.27/1.52      inference('sup+', [status(thm)], ['19', '22'])).
% 1.27/1.52  thf('24', plain,
% 1.27/1.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 1.27/1.52           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X2 @ X4)))),
% 1.27/1.52      inference('cnf', [status(esa)], [l36_xboole_1])).
% 1.27/1.52  thf('25', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 1.27/1.52           = (k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 1.27/1.52              k1_xboole_0))),
% 1.27/1.52      inference('sup+', [status(thm)], ['23', '24'])).
% 1.27/1.52  thf('26', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.52  thf(t50_xboole_1, axiom,
% 1.27/1.52    (![A:$i,B:$i,C:$i]:
% 1.27/1.52     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.27/1.52       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.27/1.52  thf('27', plain,
% 1.27/1.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.27/1.52           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 1.27/1.52              (k3_xboole_0 @ X16 @ X18)))),
% 1.27/1.52      inference('cnf', [status(esa)], [t50_xboole_1])).
% 1.27/1.52  thf('28', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 1.27/1.52           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['26', '27'])).
% 1.27/1.52  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['8', '9'])).
% 1.27/1.52  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['8', '9'])).
% 1.27/1.52  thf('31', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf('32', plain,
% 1.27/1.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 1.27/1.52           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X2 @ X4)))),
% 1.27/1.52      inference('cnf', [status(esa)], [l36_xboole_1])).
% 1.27/1.52  thf('33', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 1.27/1.52           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['31', '32'])).
% 1.27/1.52  thf('34', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 1.27/1.52           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['30', '33'])).
% 1.27/1.52  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['8', '9'])).
% 1.27/1.52  thf('36', plain,
% 1.27/1.52      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.27/1.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.27/1.52  thf('37', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.27/1.52      inference('sup+', [status(thm)], ['35', '36'])).
% 1.27/1.52  thf('38', plain,
% 1.27/1.52      (![X10 : $i, X12 : $i]:
% 1.27/1.52         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 1.27/1.52          | ~ (r1_tarski @ X10 @ X12))),
% 1.27/1.52      inference('cnf', [status(esa)], [t37_xboole_1])).
% 1.27/1.52  thf('39', plain,
% 1.27/1.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['37', '38'])).
% 1.27/1.52  thf('40', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf('41', plain,
% 1.27/1.52      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.27/1.52      inference('sup+', [status(thm)], ['39', '40'])).
% 1.27/1.52  thf('42', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.27/1.52      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.52  thf('43', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.27/1.52      inference('demod', [status(thm)], ['12', '13'])).
% 1.27/1.52  thf('44', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.27/1.52      inference('demod', [status(thm)], ['34', '41', '42', '43'])).
% 1.27/1.52  thf('45', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.27/1.52      inference('sup+', [status(thm)], ['29', '44'])).
% 1.27/1.52  thf('46', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.27/1.52           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 1.27/1.52      inference('demod', [status(thm)], ['25', '28', '45'])).
% 1.27/1.52  thf('47', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))
% 1.27/1.52           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 1.27/1.52      inference('sup+', [status(thm)], ['18', '46'])).
% 1.27/1.52  thf('48', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.27/1.52           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 1.27/1.52      inference('demod', [status(thm)], ['25', '28', '45'])).
% 1.27/1.52  thf('49', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X1 @ X0)
% 1.27/1.52           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['14', '17'])).
% 1.27/1.52  thf('50', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.27/1.52           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 1.27/1.52      inference('demod', [status(thm)], ['25', '28', '45'])).
% 1.27/1.52  thf('51', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0)
% 1.27/1.52           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 1.27/1.52      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 1.27/1.52  thf('52', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf('53', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf('54', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.27/1.52           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.27/1.52      inference('sup+', [status(thm)], ['52', '53'])).
% 1.27/1.52  thf('55', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.27/1.52      inference('sup-', [status(thm)], ['20', '21'])).
% 1.27/1.52  thf('56', plain,
% 1.27/1.52      (![X14 : $i, X15 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.27/1.52           = (k3_xboole_0 @ X14 @ X15))),
% 1.27/1.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.27/1.52  thf('57', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 1.27/1.52           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.27/1.52      inference('sup+', [status(thm)], ['55', '56'])).
% 1.27/1.52  thf('58', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.27/1.52      inference('cnf', [status(esa)], [t3_boole])).
% 1.27/1.52  thf('59', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.52  thf('60', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X0 @ X1)
% 1.27/1.52           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.27/1.52      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.27/1.52  thf('61', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.27/1.52           = (k4_xboole_0 @ X1 @ X0))),
% 1.27/1.52      inference('demod', [status(thm)], ['54', '60'])).
% 1.27/1.52  thf('62', plain,
% 1.27/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.52         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 1.27/1.52           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X2 @ X1)))),
% 1.27/1.52      inference('demod', [status(thm)], ['5', '51', '61'])).
% 1.27/1.52  thf('63', plain,
% 1.27/1.52      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.27/1.52         != (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.27/1.52      inference('demod', [status(thm)], ['0', '62'])).
% 1.27/1.52  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 1.27/1.52  
% 1.27/1.52  % SZS output end Refutation
% 1.27/1.52  
% 1.27/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
