%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RZdKhZmecO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:11 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 158 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   26
%              Number of atoms          :  693 (1283 expanded)
%              Number of equality atoms :   60 ( 116 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','32'])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['2','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','58','61'])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RZdKhZmecO
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:24:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 596 iterations in 0.520s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(t100_xboole_1, conjecture,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i,B:$i]:
% 0.75/0.98        ( ( k4_xboole_0 @ A @ B ) =
% 0.75/0.98          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.75/0.98  thf('0', plain,
% 0.75/0.98      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.75/0.98         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(t17_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.98  thf('1', plain,
% 0.75/0.98      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.75/0.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.98  thf(t45_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_tarski @ A @ B ) =>
% 0.75/0.98       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (![X10 : $i, X11 : $i]:
% 0.75/0.98         (((X11) = (k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))
% 0.75/0.98          | ~ (r1_tarski @ X10 @ X11))),
% 0.75/0.98      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.75/0.98  thf(t48_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.75/0.98           = (k3_xboole_0 @ X14 @ X15))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf('4', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.75/0.98           = (k3_xboole_0 @ X14 @ X15))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf(t47_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (![X12 : $i, X13 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.75/0.98           = (k4_xboole_0 @ X12 @ X13))),
% 0.75/0.98      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['5', '6'])).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.75/0.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.75/0.98      inference('sup+', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      (![X10 : $i, X11 : $i]:
% 0.75/0.98         (((X11) = (k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))
% 0.75/0.98          | ~ (r1_tarski @ X10 @ X11))),
% 0.75/0.98      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.75/0.98  thf('11', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0)
% 0.75/0.98           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.75/0.98              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.75/0.98           = (k3_xboole_0 @ X14 @ X15))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0)
% 0.75/0.98           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.75/0.98  thf(t94_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k2_xboole_0 @ A @ B ) =
% 0.75/0.98       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (![X25 : $i, X26 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X25 @ X26)
% 0.75/0.98           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 0.75/0.98              (k3_xboole_0 @ X25 @ X26)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.75/0.98  thf(t91_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.98       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 0.75/0.98           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      (![X25 : $i, X26 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X25 @ X26)
% 0.75/0.98           = (k5_xboole_0 @ X25 @ 
% 0.75/0.98              (k5_xboole_0 @ X26 @ (k3_xboole_0 @ X25 @ X26))))),
% 0.75/0.98      inference('demod', [status(thm)], ['15', '16'])).
% 0.75/0.98  thf(l98_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k5_xboole_0 @ A @ B ) =
% 0.75/0.98       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ X4 @ X5)
% 0.75/0.98           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['5', '6'])).
% 0.75/0.98  thf('20', plain,
% 0.75/0.98      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.75/0.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.98  thf(t85_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X19 @ X20)
% 0.75/0.98          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.98  thf(t83_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i]:
% 0.75/0.98         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.75/0.98      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k3_xboole_0 @ X0 @ X2))),
% 0.75/0.98      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.98  thf('25', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.75/0.98      inference('sup+', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['24', '25'])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.75/0.98          (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['19', '26'])).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['5', '6'])).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['27', '28'])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ 
% 0.75/0.98          (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['18', '29'])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ X4 @ X5)
% 0.75/0.98           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['30', '31'])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.75/0.98          (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.75/0.98      inference('sup+', [status(thm)], ['17', '32'])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X25 : $i, X26 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X25 @ X26)
% 0.75/0.98           = (k5_xboole_0 @ X25 @ 
% 0.75/0.98              (k5_xboole_0 @ X26 @ (k3_xboole_0 @ X25 @ X26))))),
% 0.75/0.98      inference('demod', [status(thm)], ['15', '16'])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['33', '34'])).
% 0.75/0.98  thf('36', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (r1_tarski @ X0 @ 
% 0.75/0.98          (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['14', '35'])).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0)
% 0.75/0.98           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.75/0.98  thf('38', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.75/0.98      inference('demod', [status(thm)], ['36', '37'])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X19 @ X20)
% 0.75/0.98          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['38', '39'])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i]:
% 0.75/0.98         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.75/0.98      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['40', '41'])).
% 0.75/0.98  thf(t98_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X27 : $i, X28 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X27 @ X28)
% 0.75/0.98           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.98  thf('44', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.75/0.98           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['42', '43'])).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.98  thf(commutativity_k5_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.75/0.98  thf('48', plain,
% 0.75/0.98      (![X27 : $i, X28 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X27 @ X28)
% 0.75/0.98           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X0 @ X1)
% 0.75/0.98           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('50', plain,
% 0.75/0.98      (![X10 : $i, X11 : $i]:
% 0.75/0.98         (((X11) = (k2_xboole_0 @ X10 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.75/0.98      inference('demod', [status(thm)], ['2', '49'])).
% 0.75/0.98  thf('51', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '50'])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.98  thf('53', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['51', '52'])).
% 0.75/0.98  thf('54', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ X4 @ X5)
% 0.75/0.98           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ X0 @ X1)
% 0.75/0.98           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['54', '55'])).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.75/0.98           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['53', '56'])).
% 0.75/0.98  thf('58', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.98  thf('59', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k3_xboole_0 @ X0 @ X2))),
% 0.75/0.98      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.98  thf('60', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.75/0.98           = (k3_xboole_0 @ X14 @ X15))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf('61', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['59', '60'])).
% 0.75/0.98  thf('62', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.75/0.98           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['57', '58', '61'])).
% 0.75/0.98  thf('63', plain,
% 0.75/0.98      (![X12 : $i, X13 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.75/0.98           = (k4_xboole_0 @ X12 @ X13))),
% 0.75/0.98      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.75/0.98  thf('64', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k4_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['62', '63'])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['0', '64'])).
% 0.75/0.98  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
