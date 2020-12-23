%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oo1kZtWIq1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:44 EST 2020

% Result     : Theorem 25.49s
% Output     : Refutation 25.49s
% Verified   : 
% Statistics : Number of formulae       :  578 (57428650 expanded)
%              Number of leaves         :   17 (19496862 expanded)
%              Depth                    :   76
%              Number of atoms          : 6219 (569742046 expanded)
%              Number of equality atoms :  551 (52538038 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t108_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t108_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
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

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) @ X1 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','74','75'])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
      = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('83',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('87',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','92'])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('97',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('99',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('101',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('103',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('105',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('107',plain,
    ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('111',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('119',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('121',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','117','118'])).

thf('123',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('125',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['121','122','123','134'])).

thf('136',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('137',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','117','118'])).

thf('138',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('141',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('142',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('143',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('146',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('150',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('152',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['152','153','156'])).

thf('158',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['157','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','167'])).

thf('169',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('170',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('173',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X3 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X3 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('182',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['180','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['171','184'])).

thf('186',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['168','185'])).

thf('187',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('188',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('190',plain,
    ( ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('194',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','32'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['198','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('204',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['202','205','206','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('212',plain,
    ( ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('214',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('215',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['197','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('222',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('224',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('226',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('228',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('229',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('231',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('232',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['226','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('235',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('237',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('238',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('240',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('241',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('242',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['190','191','192','238','239','240','241'])).

thf('243',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('244',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','167'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('247',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('248',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ X2 ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['246','249'])).

thf('251',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['245','250'])).

thf('252',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('253',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('255',plain,
    ( ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('257',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('258',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('259',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('260',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['255','256','257','258','259'])).

thf('261',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('262',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['244','260','261'])).

thf('263',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['143','262'])).

thf('264',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('266',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('267',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('268',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['265','268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['264','269'])).

thf('271',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('272',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('273',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('274',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['270','271','272','273'])).

thf('275',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('276',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('277',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['226','232'])).

thf('279',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['279','280'])).

thf('282',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) )
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['274','281'])).

thf('283',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('284',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('285',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('289',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('290',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['290','291'])).

thf('293',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('294',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('295',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('296',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('297',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['292','293','294','295','296'])).

thf('298',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('299',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['297','298','299'])).

thf('301',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['284','300'])).

thf('302',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','167'])).

thf('303',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['301','302'])).

thf('304',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('305',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('306',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('309',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('310',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('311',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X3 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('313',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X3 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('315',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('316',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X3 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['307','308','316'])).

thf('318',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','167'])).

thf('319',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['282','283','303','304','317','318'])).

thf('320',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['163','164','167'])).

thf('321',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('322',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('323',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ X2 )
      = X2 ) ),
    inference('sup+',[status(thm)],['321','322'])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_A ) ) @ sk_A )
      = sk_A ) ),
    inference('sup+',[status(thm)],['320','323'])).

thf('325',plain,
    ( ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['319','324'])).

thf('326',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['265','268'])).

thf('327',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('328',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['326','327'])).

thf('329',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('330',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['325','330'])).

thf('332',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['282','283','303','304','317','318'])).

thf('333',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['255','256','257','258','259'])).

thf('334',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['332','333'])).

thf('335',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['331','334'])).

thf('336',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['263','335'])).

thf('337',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['265','268'])).

thf('338',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['336','337'])).

thf('339',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['263','335'])).

thf('340',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('341',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['331','334'])).

thf('342',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['338','339','340','341'])).

thf('343',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('344',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('345',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['343','344'])).

thf('346',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['342','345'])).

thf('347',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('348',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('349',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('350',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['348','349'])).

thf('351',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['346','347'])).

thf('352',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['332','333'])).

thf('353',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('354',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('355',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('356',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','117','118'])).

thf('357',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('358',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['355','356','357'])).

thf('359',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('360',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('361',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('362',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('363',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['361','362'])).

thf('364',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['360','363'])).

thf('365',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('366',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('367',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('368',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('369',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['364','365','366','367','368'])).

thf('370',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['354','369'])).

thf('371',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('372',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','139','140'])).

thf('373',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['370','371','372'])).

thf('374',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['350','351','352','353','373'])).

thf('375',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['263','335'])).

thf('376',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['374','375'])).

thf('377',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('378',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['376','377'])).

thf('379',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['374','375'])).

thf('380',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['332','333'])).

thf('381',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['263','335'])).

thf('382',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['378','379','380','381'])).

thf('383',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('384',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['382','383'])).

thf('385',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['332','333'])).

thf('386',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['384','385'])).

thf('387',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('388',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['384','385'])).

thf('389',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['387','388'])).

thf('390',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['358','359'])).

thf('391',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['374','375'])).

thf('392',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('393',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['391','392'])).

thf('394',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('395',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['393','394'])).

thf('396',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('397',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('398',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['396','397'])).

thf('399',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('400',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['398','399'])).

thf('401',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('402',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('403',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X3 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['401','402'])).

thf('404',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['400','403'])).

thf('405',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['395','404'])).

thf('406',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['374','375'])).

thf('407',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['378','379','380','381'])).

thf('408',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['378','379','380','381'])).

thf('409',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['396','397'])).

thf('410',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['408','409'])).

thf('411',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['378','379','380','381'])).

thf('412',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['410','411'])).

thf('413',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['400','403'])).

thf('414',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('415',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X1 ) @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['413','414'])).

thf('416',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_A )
      = sk_A ) ),
    inference('sup+',[status(thm)],['412','415'])).

thf('417',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['405','406','407','416'])).

thf('418',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['393','394'])).

thf('419',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['417','418'])).

thf('420',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('421',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['265','268'])).

thf('422',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['420','421'])).

thf('423',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('424',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('425',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('426',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['422','423','424','425'])).

thf('427',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['419','426'])).

thf('428',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['405','406','407','416'])).

thf('429',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['427','428'])).

thf('430',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('431',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['429','430'])).

thf('432',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('433',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['431','432'])).

thf('434',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('435',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['433','434'])).

thf('436',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('437',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['435','436'])).

thf('438',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['417','418'])).

thf('439',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('440',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['438','439'])).

thf('441',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('442',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('443',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['437','440','441','442'])).

thf('444',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['390','443'])).

thf('445',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['384','385'])).

thf('446',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('447',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup+',[status(thm)],['445','446'])).

thf('448',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['444','447'])).

thf('449',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['389','448'])).

thf('450',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('451',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['449','450'])).

thf('452',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['438','439'])).

thf('453',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('454',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = sk_B ) ),
    inference('sup+',[status(thm)],['452','453'])).

thf('455',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['451','454'])).

thf('456',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['361','362'])).

thf('457',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['455','456'])).

thf('458',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['451','454'])).

thf('459',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('460',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['457','458','459'])).

thf('461',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['384','385'])).

thf('462',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['457','458','459'])).

thf('463',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('464',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('465',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['463','464'])).

thf('466',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['433','434'])).

thf('467',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('468',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('469',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['467','468'])).

thf('470',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('471',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['469','470'])).

thf('472',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['466','471'])).

thf('473',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['438','439'])).

thf('474',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('475',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('476',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['472','473','474','475'])).

thf('477',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('478',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['374','375'])).

thf('479',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('480',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['478','479'])).

thf('481',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['378','379','380','381'])).

thf('482',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('483',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['481','482'])).

thf('484',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','386','460','461','462','465','476','477','480','483'])).

thf('485',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','484'])).

thf('486',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('487',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['485','486'])).

thf('488',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','487'])).

thf('489',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['396','397'])).

thf('490',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('491',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['489','490'])).

thf('492',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('493',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['491','492'])).

thf('494',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('495',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['493','494'])).

thf('496',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['463','464'])).

thf('497',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('498',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['495','496','497'])).

thf('499',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('500',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['498','499'])).

thf('501',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['495','496','497'])).

thf('502',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('503',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['501','502'])).

thf('504',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('505',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['503','504'])).

thf('506',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['500','505'])).

thf('507',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['495','496','497'])).

thf('508',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ X2 )
      = X2 ) ),
    inference('sup+',[status(thm)],['321','322'])).

thf('509',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['507','508'])).

thf('510',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('511',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['509','510'])).

thf('512',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('513',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('514',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('515',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('516',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('517',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['515','516'])).

thf('518',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('519',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['511','512','513','514','517','518'])).

thf('520',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['506','519'])).

thf('521',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['500','505'])).

thf('522',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['520','521'])).

thf('523',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('524',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['522','523'])).

thf('525',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['503','504'])).

thf('526',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['524','525'])).

thf('527',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('528',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['526','527'])).

thf('529',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['495','496','497'])).

thf('530',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('531',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['529','530'])).

thf('532',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('533',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['531','532'])).

thf('534',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['528','533'])).

thf('535',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('536',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('537',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['535','536'])).

thf('538',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('539',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['537','538'])).

thf('540',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('541',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['539','540'])).

thf('542',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['534','541'])).

thf('543',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['524','525'])).

thf('544',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['531','532'])).

thf('545',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['531','532'])).

thf('546',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['528','533'])).

thf('547',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('548',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['542','543','544','545','546','547'])).

thf('549',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('550',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['548','549'])).

thf('551',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('552',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['550','551'])).

thf('553',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['478','479'])).

thf('554',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['488','552','553'])).

thf('555',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['438','439'])).

thf('556',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('557',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['555','556'])).

thf('558',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['554','557'])).

thf('559',plain,(
    $false ),
    inference(demod,[status(thm)],['0','558'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oo1kZtWIq1
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 25.49/25.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 25.49/25.72  % Solved by: fo/fo7.sh
% 25.49/25.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.49/25.72  % done 7441 iterations in 25.247s
% 25.49/25.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 25.49/25.72  % SZS output start Refutation
% 25.49/25.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 25.49/25.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 25.49/25.72  thf(sk_B_type, type, sk_B: $i).
% 25.49/25.72  thf(sk_A_type, type, sk_A: $i).
% 25.49/25.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 25.49/25.72  thf(sk_C_type, type, sk_C: $i).
% 25.49/25.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 25.49/25.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 25.49/25.72  thf(t108_xboole_1, conjecture,
% 25.49/25.72    (![A:$i,B:$i,C:$i]:
% 25.49/25.72     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 25.49/25.72  thf(zf_stmt_0, negated_conjecture,
% 25.49/25.72    (~( ![A:$i,B:$i,C:$i]:
% 25.49/25.72        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )),
% 25.49/25.72    inference('cnf.neg', [status(esa)], [t108_xboole_1])).
% 25.49/25.72  thf('0', plain, (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 25.49/25.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.49/25.72  thf(t100_xboole_1, axiom,
% 25.49/25.72    (![A:$i,B:$i]:
% 25.49/25.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 25.49/25.72  thf('1', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('2', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf(t91_xboole_1, axiom,
% 25.49/25.72    (![A:$i,B:$i,C:$i]:
% 25.49/25.72     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 25.49/25.72       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 25.49/25.72  thf('3', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('4', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['2', '3'])).
% 25.49/25.72  thf('5', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 25.49/25.72           (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['1', '4'])).
% 25.49/25.72  thf(commutativity_k3_xboole_0, axiom,
% 25.49/25.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 25.49/25.72  thf('6', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf(t49_xboole_1, axiom,
% 25.49/25.72    (![A:$i,B:$i,C:$i]:
% 25.49/25.72     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 25.49/25.72       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 25.49/25.72  thf('7', plain,
% 25.49/25.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 25.49/25.72      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.49/25.72  thf('8', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('9', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 25.49/25.72           (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))))),
% 25.49/25.72      inference('demod', [status(thm)], ['5', '8'])).
% 25.49/25.72  thf('10', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('11', plain,
% 25.49/25.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 25.49/25.72      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.49/25.72  thf('12', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('13', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('14', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['12', '13'])).
% 25.49/25.72  thf('15', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 25.49/25.72           (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 25.49/25.72           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['9', '14'])).
% 25.49/25.72  thf('16', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf(t17_xboole_1, axiom,
% 25.49/25.72    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 25.49/25.72  thf('17', plain,
% 25.49/25.72      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 25.49/25.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 25.49/25.72  thf(t12_xboole_1, axiom,
% 25.49/25.72    (![A:$i,B:$i]:
% 25.49/25.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 25.49/25.72  thf('18', plain,
% 25.49/25.72      (![X4 : $i, X5 : $i]:
% 25.49/25.72         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 25.49/25.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 25.49/25.72  thf('19', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.72      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.72  thf('20', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['16', '19'])).
% 25.49/25.72  thf('21', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('22', plain, ((r1_tarski @ sk_A @ sk_B)),
% 25.49/25.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.49/25.72  thf('23', plain,
% 25.49/25.72      (![X4 : $i, X5 : $i]:
% 25.49/25.72         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 25.49/25.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 25.49/25.72  thf('24', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 25.49/25.72      inference('sup-', [status(thm)], ['22', '23'])).
% 25.49/25.72  thf(t95_xboole_1, axiom,
% 25.49/25.72    (![A:$i,B:$i]:
% 25.49/25.72     ( ( k3_xboole_0 @ A @ B ) =
% 25.49/25.72       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 25.49/25.72  thf('25', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 25.49/25.72              (k2_xboole_0 @ X14 @ X15)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t95_xboole_1])).
% 25.49/25.72  thf('26', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['24', '25'])).
% 25.49/25.72  thf('27', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('28', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['26', '27'])).
% 25.49/25.72  thf('29', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('30', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['28', '29'])).
% 25.49/25.72  thf('31', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('32', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('demod', [status(thm)], ['30', '31'])).
% 25.49/25.72  thf('33', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ sk_B @ X0))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['21', '32'])).
% 25.49/25.72  thf('34', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['2', '3'])).
% 25.49/25.72  thf('35', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ sk_B @ X0))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ 
% 25.49/25.72               (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['33', '34'])).
% 25.49/25.72  thf('36', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf(t98_xboole_1, axiom,
% 25.49/25.72    (![A:$i,B:$i]:
% 25.49/25.72     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 25.49/25.72  thf('37', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('38', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ 
% 25.49/25.72              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['36', '37'])).
% 25.49/25.72  thf('39', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ 
% 25.49/25.72           (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k5_xboole_0 @ sk_A @ 
% 25.49/25.72             (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))) @ 
% 25.49/25.72           X1)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ 
% 25.49/25.72               (k5_xboole_0 @ sk_A @ 
% 25.49/25.72                (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))) @ 
% 25.49/25.72               (k4_xboole_0 @ X1 @ 
% 25.49/25.72                (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72                 (k3_xboole_0 @ sk_B @ X0))))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['35', '38'])).
% 25.49/25.72  thf('40', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ sk_B @ X0))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ 
% 25.49/25.72               (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['33', '34'])).
% 25.49/25.72  thf('41', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('42', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('43', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ 
% 25.49/25.72           (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72            (k3_xboole_0 @ sk_B @ X0)) @ 
% 25.49/25.72           X1)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ 
% 25.49/25.72               (k5_xboole_0 @ sk_B @ 
% 25.49/25.72                (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 25.49/25.72                 (k4_xboole_0 @ X1 @ 
% 25.49/25.72                  (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72                   (k3_xboole_0 @ sk_B @ X0))))))))),
% 25.49/25.72      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 25.49/25.72  thf('44', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('45', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('46', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.72  thf('47', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ sk_B @ X0))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['21', '32'])).
% 25.49/25.72  thf('48', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ 
% 25.49/25.72             (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['46', '47'])).
% 25.49/25.72  thf('49', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('50', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('51', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ 
% 25.49/25.72             (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['48', '49', '50'])).
% 25.49/25.72  thf('52', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 25.49/25.72              (k2_xboole_0 @ X14 @ X15)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t95_xboole_1])).
% 25.49/25.72  thf('53', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('54', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ X14 @ 
% 25.49/25.72              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.72      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.72  thf('55', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['2', '3'])).
% 25.49/25.72  thf('56', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 25.49/25.72           (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 25.49/25.72           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['54', '55'])).
% 25.49/25.72  thf('57', plain,
% 25.49/25.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 25.49/25.72      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.49/25.72  thf('58', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('59', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['57', '58'])).
% 25.49/25.72  thf('60', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('61', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['59', '60'])).
% 25.49/25.72  thf('62', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 25.49/25.72           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 25.49/25.72           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['56', '61'])).
% 25.49/25.72  thf('63', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ 
% 25.49/25.72             (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['48', '49', '50'])).
% 25.49/25.72  thf('64', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('65', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)) @ 
% 25.49/25.72           X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ 
% 25.49/25.72               (k5_xboole_0 @ sk_B @ 
% 25.49/25.72                (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))) @ 
% 25.49/25.72               X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['63', '64'])).
% 25.49/25.72  thf('66', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('67', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)) @ 
% 25.49/25.72           X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ 
% 25.49/25.72               (k5_xboole_0 @ 
% 25.49/25.72                (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0))))),
% 25.49/25.72      inference('demod', [status(thm)], ['65', '66'])).
% 25.49/25.72  thf('68', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ 
% 25.49/25.72          (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ 
% 25.49/25.72             (k3_xboole_0 @ sk_B @ 
% 25.49/25.72              (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['62', '67'])).
% 25.49/25.72  thf('69', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('70', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('71', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('72', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('73', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.72      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.72  thf('74', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)
% 25.49/25.72           = (X1))),
% 25.49/25.72      inference('sup+', [status(thm)], ['72', '73'])).
% 25.49/25.72  thf('75', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('76', plain,
% 25.49/25.72      (((sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ 
% 25.49/25.72             (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['68', '69', '70', '71', '74', '75'])).
% 25.49/25.72  thf('77', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ X14 @ 
% 25.49/25.72              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.72      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.72  thf('78', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('demod', [status(thm)], ['30', '31'])).
% 25.49/25.72  thf('79', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['77', '78'])).
% 25.49/25.72  thf('80', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('81', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['79', '80'])).
% 25.49/25.72  thf('82', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.72  thf('83', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('84', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['82', '83'])).
% 25.49/25.72  thf('85', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))
% 25.49/25.72           = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['81', '84'])).
% 25.49/25.72  thf('86', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('87', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('88', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['86', '87'])).
% 25.49/25.72  thf('89', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ 
% 25.49/25.72               (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['85', '88'])).
% 25.49/25.72  thf('90', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 25.49/25.72      inference('sup-', [status(thm)], ['22', '23'])).
% 25.49/25.72  thf('91', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ X14 @ 
% 25.49/25.72              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.72      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.72  thf('92', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_B @ X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ 
% 25.49/25.72               (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['89', '90', '91'])).
% 25.49/25.72  thf('93', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['76', '92'])).
% 25.49/25.72  thf('94', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['26', '27'])).
% 25.49/25.72  thf('95', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['93', '94'])).
% 25.49/25.72  thf('96', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('97', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['95', '96'])).
% 25.49/25.72  thf('98', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.72  thf('99', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k4_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['97', '98'])).
% 25.49/25.72  thf('100', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('101', plain,
% 25.49/25.72      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72         sk_B)
% 25.49/25.72         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['99', '100'])).
% 25.49/25.72  thf('102', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.72      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.72  thf('103', plain,
% 25.49/25.72      (((sk_B)
% 25.49/25.72         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['101', '102'])).
% 25.49/25.72  thf('104', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['2', '3'])).
% 25.49/25.72  thf('105', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ sk_A)) = (k5_xboole_0 @ sk_B @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['103', '104'])).
% 25.49/25.72  thf('106', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['86', '87'])).
% 25.49/25.72  thf('107', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['105', '106'])).
% 25.49/25.72  thf('108', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['16', '19'])).
% 25.49/25.72  thf('109', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('110', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.72      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.72  thf('111', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 25.49/25.72              (k2_xboole_0 @ X14 @ X15)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t95_xboole_1])).
% 25.49/25.72  thf('112', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['110', '111'])).
% 25.49/25.72  thf('113', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('114', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ X0))),
% 25.49/25.72      inference('demod', [status(thm)], ['112', '113'])).
% 25.49/25.72  thf('115', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('116', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['114', '115'])).
% 25.49/25.72  thf('117', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['109', '116'])).
% 25.49/25.72  thf('118', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('119', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['107', '108', '117', '118'])).
% 25.49/25.72  thf('120', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['114', '115'])).
% 25.49/25.72  thf('121', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['119', '120'])).
% 25.49/25.72  thf('122', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['107', '108', '117', '118'])).
% 25.49/25.72  thf('123', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('124', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['16', '19'])).
% 25.49/25.72  thf('125', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 25.49/25.72              (k2_xboole_0 @ X14 @ X15)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t95_xboole_1])).
% 25.49/25.72  thf('126', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['124', '125'])).
% 25.49/25.72  thf('127', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('128', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 25.49/25.72           = (k5_xboole_0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ X0))),
% 25.49/25.72      inference('demod', [status(thm)], ['126', '127'])).
% 25.49/25.72  thf('129', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('130', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['128', '129'])).
% 25.49/25.72  thf('131', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['82', '83'])).
% 25.49/25.72  thf('132', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['130', '131'])).
% 25.49/25.72  thf('133', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('134', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 25.49/25.72           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['132', '133'])).
% 25.49/25.72  thf('135', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)))
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 25.49/25.72      inference('demod', [status(thm)], ['121', '122', '123', '134'])).
% 25.49/25.72  thf('136', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['93', '94'])).
% 25.49/25.72  thf('137', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['107', '108', '117', '118'])).
% 25.49/25.72  thf('138', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)))
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['136', '137'])).
% 25.49/25.72  thf('139', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 25.49/25.72      inference('demod', [status(thm)], ['135', '138'])).
% 25.49/25.72  thf('140', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('141', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('142', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('143', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['141', '142'])).
% 25.49/25.72  thf('144', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('145', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['114', '115'])).
% 25.49/25.72  thf('146', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ 
% 25.49/25.72         (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72            (k5_xboole_0 @ sk_A @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['144', '145'])).
% 25.49/25.72  thf('147', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('148', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 25.49/25.72           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['132', '133'])).
% 25.49/25.72  thf('149', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('150', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 25.49/25.72  thf('151', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('152', plain,
% 25.49/25.72      (((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72            (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['150', '151'])).
% 25.49/25.72  thf('153', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.72      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.72  thf('154', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['57', '58'])).
% 25.49/25.72  thf('155', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('demod', [status(thm)], ['30', '31'])).
% 25.49/25.72  thf('156', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ 
% 25.49/25.72               (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ X1 @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['154', '155'])).
% 25.49/25.72  thf('157', plain,
% 25.49/25.72      (((sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ 
% 25.49/25.72             (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['152', '153', '156'])).
% 25.49/25.72  thf('158', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('159', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('demod', [status(thm)], ['30', '31'])).
% 25.49/25.72  thf('160', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k4_xboole_0 @ X0 @ sk_B))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['158', '159'])).
% 25.49/25.72  thf('161', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['2', '3'])).
% 25.49/25.72  thf('162', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k4_xboole_0 @ X0 @ sk_B))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ 
% 25.49/25.72               (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['160', '161'])).
% 25.49/25.72  thf('163', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72         (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('sup+', [status(thm)], ['157', '162'])).
% 25.49/25.72  thf('164', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('165', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('166', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.72  thf('167', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k5_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 25.49/25.72              (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['165', '166'])).
% 25.49/25.72  thf('168', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['163', '164', '167'])).
% 25.49/25.72  thf('169', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('170', plain,
% 25.49/25.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 25.49/25.72      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.49/25.72  thf('171', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_A @ 
% 25.49/25.72           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0))
% 25.49/25.72           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['169', '170'])).
% 25.49/25.72  thf('172', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('173', plain,
% 25.49/25.72      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 25.49/25.72      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.49/25.72  thf('174', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X3))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3))),
% 25.49/25.72      inference('sup+', [status(thm)], ['172', '173'])).
% 25.49/25.72  thf('175', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('176', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X3))
% 25.49/25.72           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('demod', [status(thm)], ['174', '175'])).
% 25.49/25.72  thf('177', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('178', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('179', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('180', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X3))
% 25.49/25.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['176', '179'])).
% 25.49/25.72  thf('181', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('182', plain,
% 25.49/25.72      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 25.49/25.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 25.49/25.72  thf('183', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)),
% 25.49/25.72      inference('sup+', [status(thm)], ['181', '182'])).
% 25.49/25.72  thf('184', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         (r1_tarski @ 
% 25.49/25.72          (k3_xboole_0 @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 25.49/25.72          (k4_xboole_0 @ X2 @ X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['180', '183'])).
% 25.49/25.72  thf('185', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 25.49/25.72          (k4_xboole_0 @ sk_B @ X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['171', '184'])).
% 25.49/25.72  thf('186', plain,
% 25.49/25.72      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('sup+', [status(thm)], ['168', '185'])).
% 25.49/25.72  thf('187', plain,
% 25.49/25.72      (![X4 : $i, X5 : $i]:
% 25.49/25.72         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 25.49/25.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 25.49/25.72  thf('188', plain,
% 25.49/25.72      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ sk_A)) = (k4_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('sup-', [status(thm)], ['186', '187'])).
% 25.49/25.72  thf('189', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ X14 @ 
% 25.49/25.72              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.72      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.72  thf('190', plain,
% 25.49/25.72      (((k3_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.72            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72             (k4_xboole_0 @ sk_B @ sk_A))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['188', '189'])).
% 25.49/25.72  thf('191', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('192', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('193', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['114', '115'])).
% 25.49/25.72  thf('194', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['2', '3'])).
% 25.49/25.72  thf('195', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['193', '194'])).
% 25.49/25.72  thf('196', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('197', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X1))
% 25.49/25.72           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['195', '196'])).
% 25.49/25.72  thf('198', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ 
% 25.49/25.72             (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['48', '49', '50'])).
% 25.49/25.72  thf('199', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ sk_B @ X0))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['21', '32'])).
% 25.49/25.72  thf('200', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['82', '83'])).
% 25.49/25.72  thf('201', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72           (k3_xboole_0 @ sk_B @ X0))
% 25.49/25.72           = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ 
% 25.49/25.72               (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['199', '200'])).
% 25.49/25.72  thf('202', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72            (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['198', '201'])).
% 25.49/25.72  thf('203', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('204', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('205', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['203', '204'])).
% 25.49/25.72  thf('206', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('207', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('208', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['59', '60'])).
% 25.49/25.72  thf('209', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 25.49/25.72           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['207', '208'])).
% 25.49/25.72  thf('210', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['202', '205', '206', '209'])).
% 25.49/25.72  thf('211', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['86', '87'])).
% 25.49/25.72  thf('212', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['210', '211'])).
% 25.49/25.72  thf('213', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 25.49/25.72      inference('sup-', [status(thm)], ['22', '23'])).
% 25.49/25.72  thf('214', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('215', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 25.49/25.72      inference('demod', [status(thm)], ['212', '213', '214'])).
% 25.49/25.72  thf('216', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('217', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72           X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ 
% 25.49/25.72               (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['215', '216'])).
% 25.49/25.72  thf('218', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72         (k5_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ 
% 25.49/25.72             (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['197', '217'])).
% 25.49/25.72  thf('219', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 25.49/25.72           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['132', '133'])).
% 25.49/25.72  thf('220', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('221', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('222', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ 
% 25.49/25.72             (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 25.49/25.72  thf('223', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k4_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['97', '98'])).
% 25.49/25.72  thf('224', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ 
% 25.49/25.72             (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['222', '223'])).
% 25.49/25.72  thf('225', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('226', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 25.49/25.72      inference('demod', [status(thm)], ['224', '225'])).
% 25.49/25.72  thf('227', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('228', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['57', '58'])).
% 25.49/25.72  thf('229', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['227', '228'])).
% 25.49/25.72  thf('230', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 25.49/25.72           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['207', '208'])).
% 25.49/25.72  thf('231', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('232', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['229', '230', '231'])).
% 25.49/25.72  thf('233', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['226', '232'])).
% 25.49/25.72  thf('234', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))
% 25.49/25.72           = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['81', '84'])).
% 25.49/25.72  thf('235', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72            (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['233', '234'])).
% 25.49/25.72  thf('236', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('237', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 25.49/25.72      inference('sup-', [status(thm)], ['22', '23'])).
% 25.49/25.72  thf('238', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ sk_A)) = (k5_xboole_0 @ sk_B @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['235', '236', '237'])).
% 25.49/25.72  thf('239', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('240', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['26', '27'])).
% 25.49/25.72  thf('241', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('242', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k4_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)],
% 25.49/25.72                ['190', '191', '192', '238', '239', '240', '241'])).
% 25.49/25.72  thf('243', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['57', '58'])).
% 25.49/25.72  thf('244', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_A @ 
% 25.49/25.72         (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A)))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['242', '243'])).
% 25.49/25.72  thf('245', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['163', '164', '167'])).
% 25.49/25.72  thf('246', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_A @ 
% 25.49/25.72           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0))
% 25.49/25.72           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['169', '170'])).
% 25.49/25.72  thf('247', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('248', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)),
% 25.49/25.72      inference('sup+', [status(thm)], ['181', '182'])).
% 25.49/25.72  thf('249', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         (r1_tarski @ 
% 25.49/25.72          (k3_xboole_0 @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 25.49/25.72          X2)),
% 25.49/25.72      inference('sup+', [status(thm)], ['247', '248'])).
% 25.49/25.72  thf('250', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) @ sk_B)),
% 25.49/25.72      inference('sup+', [status(thm)], ['246', '249'])).
% 25.49/25.72  thf('251', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_B)),
% 25.49/25.72      inference('sup+', [status(thm)], ['245', '250'])).
% 25.49/25.72  thf('252', plain,
% 25.49/25.72      (![X4 : $i, X5 : $i]:
% 25.49/25.72         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 25.49/25.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 25.49/25.72  thf('253', plain,
% 25.49/25.72      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_B) = (sk_B))),
% 25.49/25.72      inference('sup-', [status(thm)], ['251', '252'])).
% 25.49/25.72  thf('254', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ X14 @ 
% 25.49/25.72              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.72      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.72  thf('255', plain,
% 25.49/25.72      (((k3_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.72            (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['253', '254'])).
% 25.49/25.72  thf('256', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('257', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('258', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['26', '27'])).
% 25.49/25.72  thf('259', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('260', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['255', '256', '257', '258', '259'])).
% 25.49/25.72  thf('261', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['141', '142'])).
% 25.49/25.72  thf('262', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['244', '260', '261'])).
% 25.49/25.72  thf('263', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['143', '262'])).
% 25.49/25.72  thf('264', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('265', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.72  thf('266', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('267', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('268', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ 
% 25.49/25.72              (k5_xboole_0 @ X1 @ (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['266', '267'])).
% 25.49/25.72  thf('269', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['265', '268'])).
% 25.49/25.72  thf('270', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 25.49/25.72           (k3_xboole_0 @ X1 @ X0))
% 25.49/25.72           = (k5_xboole_0 @ X1 @ 
% 25.49/25.72              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['264', '269'])).
% 25.49/25.72  thf('271', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('272', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('273', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['12', '13'])).
% 25.49/25.72  thf('274', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 25.49/25.72           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('demod', [status(thm)], ['270', '271', '272', '273'])).
% 25.49/25.72  thf('275', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))),
% 25.49/25.72      inference('demod', [status(thm)], ['212', '213', '214'])).
% 25.49/25.72  thf('276', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['229', '230', '231'])).
% 25.49/25.72  thf('277', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['275', '276'])).
% 25.49/25.72  thf('278', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['226', '232'])).
% 25.49/25.72  thf('279', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['277', '278'])).
% 25.49/25.72  thf('280', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('281', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_B @ 
% 25.49/25.72           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['279', '280'])).
% 25.49/25.72  thf('282', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ 
% 25.49/25.72         (k4_xboole_0 @ sk_A @ 
% 25.49/25.72          (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))))
% 25.49/25.72         = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['274', '281'])).
% 25.49/25.72  thf('283', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['229', '230', '231'])).
% 25.49/25.72  thf('284', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['229', '230', '231'])).
% 25.49/25.72  thf('285', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('286', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ 
% 25.49/25.72               (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ X1 @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['154', '155'])).
% 25.49/25.72  thf('287', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k4_xboole_0 @ X0 @ sk_B))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ 
% 25.49/25.72               (k2_xboole_0 @ sk_B @ 
% 25.49/25.72                (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['285', '286'])).
% 25.49/25.72  thf('288', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('289', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('290', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_A @ 
% 25.49/25.72           (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ 
% 25.49/25.72               (k2_xboole_0 @ sk_B @ 
% 25.49/25.72                (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)))))),
% 25.49/25.72      inference('demod', [status(thm)], ['287', '288', '289'])).
% 25.49/25.72  thf('291', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k4_xboole_0 @ X0 @ sk_B))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_A @ 
% 25.49/25.72               (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['160', '161'])).
% 25.49/25.72  thf('292', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k4_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 25.49/25.72            sk_B))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k3_xboole_0 @ sk_A @ 
% 25.49/25.72               (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['290', '291'])).
% 25.49/25.72  thf('293', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('294', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('295', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('296', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('297', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k3_xboole_0 @ X0 @ 
% 25.49/25.72            (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))))
% 25.49/25.72           = (k4_xboole_0 @ sk_A @ 
% 25.49/25.72              (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B))))),
% 25.49/25.72      inference('demod', [status(thm)], ['292', '293', '294', '295', '296'])).
% 25.49/25.72  thf('298', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('299', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.72  thf('300', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 25.49/25.72           = (k4_xboole_0 @ sk_A @ 
% 25.49/25.72              (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B))))),
% 25.49/25.72      inference('demod', [status(thm)], ['297', '298', '299'])).
% 25.49/25.72  thf('301', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['284', '300'])).
% 25.49/25.72  thf('302', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['163', '164', '167'])).
% 25.49/25.72  thf('303', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('sup+', [status(thm)], ['301', '302'])).
% 25.49/25.72  thf('304', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('305', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('306', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('307', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ 
% 25.49/25.72           (k4_xboole_0 @ sk_A @ X0))
% 25.49/25.72           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['305', '306'])).
% 25.49/25.72  thf('308', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('309', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('310', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('311', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X3))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3))),
% 25.49/25.72      inference('sup+', [status(thm)], ['309', '310'])).
% 25.49/25.72  thf('312', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('313', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X3))
% 25.49/25.72           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('demod', [status(thm)], ['311', '312'])).
% 25.49/25.72  thf('314', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('315', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('316', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X3) @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['313', '314', '315'])).
% 25.49/25.72  thf('317', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_A @ 
% 25.49/25.72           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_B))
% 25.49/25.72           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 25.49/25.72      inference('demod', [status(thm)], ['307', '308', '316'])).
% 25.49/25.72  thf('318', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['163', '164', '167'])).
% 25.49/25.72  thf('319', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)],
% 25.49/25.72                ['282', '283', '303', '304', '317', '318'])).
% 25.49/25.72  thf('320', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['163', '164', '167'])).
% 25.49/25.72  thf('321', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.72  thf('322', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)
% 25.49/25.72           = (X1))),
% 25.49/25.72      inference('sup+', [status(thm)], ['72', '73'])).
% 25.49/25.72  thf('323', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ 
% 25.49/25.72           (k3_xboole_0 @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 25.49/25.72           X2) = (X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['321', '322'])).
% 25.49/25.72  thf('324', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_A)) @ 
% 25.49/25.72           sk_A) = (sk_A))),
% 25.49/25.72      inference('sup+', [status(thm)], ['320', '323'])).
% 25.49/25.72  thf('325', plain,
% 25.49/25.72      (((k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A) = (sk_A))),
% 25.49/25.72      inference('sup+', [status(thm)], ['319', '324'])).
% 25.49/25.72  thf('326', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['265', '268'])).
% 25.49/25.72  thf('327', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ 
% 25.49/25.72              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['36', '37'])).
% 25.49/25.72  thf('328', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['326', '327'])).
% 25.49/25.72  thf('329', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('330', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 25.49/25.72           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['328', '329'])).
% 25.49/25.72  thf('331', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_A)) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['325', '330'])).
% 25.49/25.72  thf('332', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)],
% 25.49/25.72                ['282', '283', '303', '304', '317', '318'])).
% 25.49/25.72  thf('333', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_A))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['255', '256', '257', '258', '259'])).
% 25.49/25.72  thf('334', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['332', '333'])).
% 25.49/25.72  thf('335', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['331', '334'])).
% 25.49/25.72  thf('336', plain,
% 25.49/25.72      (((sk_A) = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['263', '335'])).
% 25.49/25.72  thf('337', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['265', '268'])).
% 25.49/25.72  thf('338', plain,
% 25.49/25.72      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72            (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['336', '337'])).
% 25.49/25.72  thf('339', plain,
% 25.49/25.72      (((sk_A) = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['263', '335'])).
% 25.49/25.72  thf('340', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('341', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['331', '334'])).
% 25.49/25.72  thf('342', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['338', '339', '340', '341'])).
% 25.49/25.72  thf('343', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['229', '230', '231'])).
% 25.49/25.72  thf('344', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('345', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_B @ 
% 25.49/25.72           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['343', '344'])).
% 25.49/25.72  thf('346', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ sk_A)
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['342', '345'])).
% 25.49/25.72  thf('347', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.72  thf('348', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['346', '347'])).
% 25.49/25.72  thf('349', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['114', '115'])).
% 25.49/25.72  thf('350', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ 
% 25.49/25.72         (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))
% 25.49/25.72         = (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72            (k5_xboole_0 @ sk_A @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['348', '349'])).
% 25.49/25.72  thf('351', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['346', '347'])).
% 25.49/25.72  thf('352', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['332', '333'])).
% 25.49/25.72  thf('353', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 25.49/25.72           (k4_xboole_0 @ X0 @ sk_B))
% 25.49/25.72           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.72              (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ X0))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['158', '159'])).
% 25.49/25.72  thf('354', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['229', '230', '231'])).
% 25.49/25.72  thf('355', plain,
% 25.49/25.72      (((sk_B)
% 25.49/25.72         = (k5_xboole_0 @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 25.49/25.72            (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['101', '102'])).
% 25.49/25.72  thf('356', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['107', '108', '117', '118'])).
% 25.49/25.72  thf('357', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('358', plain,
% 25.49/25.72      (((sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72             (k4_xboole_0 @ sk_B @ sk_A))))),
% 25.49/25.72      inference('demod', [status(thm)], ['355', '356', '357'])).
% 25.49/25.72  thf('359', plain,
% 25.49/25.72      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.72         (k4_xboole_0 @ sk_B @ sk_A)) = (k5_xboole_0 @ sk_B @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['235', '236', '237'])).
% 25.49/25.72  thf('360', plain,
% 25.49/25.72      (((sk_B) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['358', '359'])).
% 25.49/25.72  thf('361', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ X14 @ 
% 25.49/25.72              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.72      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.72  thf('362', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('363', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ 
% 25.49/25.72              (k5_xboole_0 @ X1 @ 
% 25.49/25.72               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['361', '362'])).
% 25.49/25.72  thf('364', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)) @ 
% 25.49/25.72           X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_B @ 
% 25.49/25.72              (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_B) @ 
% 25.49/25.72               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.72      inference('sup+', [status(thm)], ['360', '363'])).
% 25.49/25.72  thf('365', plain,
% 25.49/25.72      (((sk_B) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['358', '359'])).
% 25.49/25.72  thf('366', plain,
% 25.49/25.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.72           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.72  thf('367', plain,
% 25.49/25.72      (![X14 : $i, X15 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.72           = (k5_xboole_0 @ X14 @ 
% 25.49/25.72              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.72      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.72  thf('368', plain,
% 25.49/25.72      (![X2 : $i, X3 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.72  thf('369', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ sk_B @ X0)
% 25.49/25.72           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['364', '365', '366', '367', '368'])).
% 25.49/25.72  thf('370', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['354', '369'])).
% 25.49/25.72  thf('371', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.72           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.72  thf('372', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 25.49/25.72         = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['51', '139', '140'])).
% 25.49/25.72  thf('373', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ sk_B)
% 25.49/25.72         = (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.72      inference('demod', [status(thm)], ['370', '371', '372'])).
% 25.49/25.72  thf('374', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['350', '351', '352', '353', '373'])).
% 25.49/25.72  thf('375', plain,
% 25.49/25.72      (((sk_A) = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['263', '335'])).
% 25.49/25.72  thf('376', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['374', '375'])).
% 25.49/25.72  thf('377', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['114', '115'])).
% 25.49/25.72  thf('378', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ 
% 25.49/25.72         (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.72         = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_A)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['376', '377'])).
% 25.49/25.72  thf('379', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['374', '375'])).
% 25.49/25.72  thf('380', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['332', '333'])).
% 25.49/25.72  thf('381', plain,
% 25.49/25.72      (((sk_A) = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['263', '335'])).
% 25.49/25.72  thf('382', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['378', '379', '380', '381'])).
% 25.49/25.72  thf('383', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.72  thf('384', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ sk_A) = (k5_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.72      inference('sup+', [status(thm)], ['382', '383'])).
% 25.49/25.72  thf('385', plain,
% 25.49/25.72      (((k5_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['332', '333'])).
% 25.49/25.72  thf('386', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['384', '385'])).
% 25.49/25.72  thf('387', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['229', '230', '231'])).
% 25.49/25.72  thf('388', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['384', '385'])).
% 25.49/25.72  thf('389', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_A))
% 25.49/25.72         = (k2_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['387', '388'])).
% 25.49/25.72  thf('390', plain,
% 25.49/25.72      (((sk_B) = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_B)))),
% 25.49/25.72      inference('demod', [status(thm)], ['358', '359'])).
% 25.49/25.72  thf('391', plain,
% 25.49/25.72      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.72      inference('demod', [status(thm)], ['374', '375'])).
% 25.49/25.72  thf('392', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 25.49/25.72      inference('sup+', [status(thm)], ['16', '19'])).
% 25.49/25.72  thf('393', plain,
% 25.49/25.72      (((k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('sup+', [status(thm)], ['391', '392'])).
% 25.49/25.72  thf('394', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['59', '60'])).
% 25.49/25.72  thf('395', plain,
% 25.49/25.72      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.72         = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.72      inference('demod', [status(thm)], ['393', '394'])).
% 25.49/25.72  thf('396', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 25.49/25.72           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 25.49/25.72           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.72      inference('demod', [status(thm)], ['56', '61'])).
% 25.49/25.72  thf('397', plain,
% 25.49/25.72      (![X16 : $i, X17 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.72           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.72  thf('398', plain,
% 25.49/25.72      (![X0 : $i]:
% 25.49/25.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 25.49/25.72           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 25.49/25.72      inference('sup+', [status(thm)], ['396', '397'])).
% 25.49/25.72  thf('399', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.72           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.72      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.72  thf('400', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 25.49/25.72           = (k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) @ X1))),
% 25.49/25.72      inference('sup+', [status(thm)], ['398', '399'])).
% 25.49/25.72  thf('401', plain,
% 25.49/25.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.73           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.73      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.73  thf('402', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 25.49/25.73           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['10', '11'])).
% 25.49/25.73  thf('403', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 25.49/25.73           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X3 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['401', '402'])).
% 25.49/25.73  thf('404', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 25.49/25.73           = (k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) @ X1))),
% 25.49/25.73      inference('demod', [status(thm)], ['400', '403'])).
% 25.49/25.73  thf('405', plain,
% 25.49/25.73      (((k3_xboole_0 @ sk_A @ 
% 25.49/25.73         (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))
% 25.49/25.73         = (k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A) @ 
% 25.49/25.73            (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['395', '404'])).
% 25.49/25.73  thf('406', plain,
% 25.49/25.73      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['374', '375'])).
% 25.49/25.73  thf('407', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['378', '379', '380', '381'])).
% 25.49/25.73  thf('408', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['378', '379', '380', '381'])).
% 25.49/25.73  thf('409', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 25.49/25.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['396', '397'])).
% 25.49/25.73  thf('410', plain,
% 25.49/25.73      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A)
% 25.49/25.73         = (k3_xboole_0 @ sk_A @ sk_A))),
% 25.49/25.73      inference('sup+', [status(thm)], ['408', '409'])).
% 25.49/25.73  thf('411', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['378', '379', '380', '381'])).
% 25.49/25.73  thf('412', plain,
% 25.49/25.73      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_A) = (sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['410', '411'])).
% 25.49/25.73  thf('413', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 25.49/25.73           = (k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) @ X1))),
% 25.49/25.73      inference('demod', [status(thm)], ['400', '403'])).
% 25.49/25.73  thf('414', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.73      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.73  thf('415', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ 
% 25.49/25.73           (k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X1) @ X0) @ 
% 25.49/25.73           X1) = (X1))),
% 25.49/25.73      inference('sup+', [status(thm)], ['413', '414'])).
% 25.49/25.73  thf('416', plain,
% 25.49/25.73      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_A) = (sk_A))),
% 25.49/25.73      inference('sup+', [status(thm)], ['412', '415'])).
% 25.49/25.73  thf('417', plain,
% 25.49/25.73      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.73      inference('demod', [status(thm)], ['405', '406', '407', '416'])).
% 25.49/25.73  thf('418', plain,
% 25.49/25.73      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.73         = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['393', '394'])).
% 25.49/25.73  thf('419', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.73      inference('sup+', [status(thm)], ['417', '418'])).
% 25.49/25.73  thf('420', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.73  thf('421', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['265', '268'])).
% 25.49/25.73  thf('422', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 25.49/25.73           (k3_xboole_0 @ X0 @ X1))
% 25.49/25.73           = (k5_xboole_0 @ X1 @ 
% 25.49/25.73              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['420', '421'])).
% 25.49/25.73  thf('423', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.73  thf('424', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 25.49/25.73           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 25.49/25.73      inference('sup+', [status(thm)], ['6', '7'])).
% 25.49/25.73  thf('425', plain,
% 25.49/25.73      (![X2 : $i, X3 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.73           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.73  thf('426', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 25.49/25.73           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 25.49/25.73      inference('demod', [status(thm)], ['422', '423', '424', '425'])).
% 25.49/25.73  thf('427', plain,
% 25.49/25.73      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 25.49/25.73         = (k4_xboole_0 @ sk_B @ 
% 25.49/25.73            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['419', '426'])).
% 25.49/25.73  thf('428', plain,
% 25.49/25.73      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.73      inference('demod', [status(thm)], ['405', '406', '407', '416'])).
% 25.49/25.73  thf('429', plain,
% 25.49/25.73      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 25.49/25.73         = (k4_xboole_0 @ sk_B @ sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['427', '428'])).
% 25.49/25.73  thf('430', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('431', plain,
% 25.49/25.73      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.73         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['429', '430'])).
% 25.49/25.73  thf('432', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('433', plain,
% 25.49/25.73      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.73         = (k2_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['431', '432'])).
% 25.49/25.73  thf('434', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 25.49/25.73      inference('sup-', [status(thm)], ['22', '23'])).
% 25.49/25.73  thf('435', plain,
% 25.49/25.73      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['433', '434'])).
% 25.49/25.73  thf('436', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ X14 @ 
% 25.49/25.73              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.73      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.73  thf('437', plain,
% 25.49/25.73      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))
% 25.49/25.73         = (k5_xboole_0 @ sk_A @ 
% 25.49/25.73            (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_B)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['435', '436'])).
% 25.49/25.73  thf('438', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.73      inference('sup+', [status(thm)], ['417', '418'])).
% 25.49/25.73  thf('439', plain,
% 25.49/25.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 25.49/25.73           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 25.49/25.73      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.49/25.73  thf('440', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 25.49/25.73           = (k4_xboole_0 @ sk_A @ X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['438', '439'])).
% 25.49/25.73  thf('441', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['86', '87'])).
% 25.49/25.73  thf('442', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 25.49/25.73      inference('sup-', [status(thm)], ['22', '23'])).
% 25.49/25.73  thf('443', plain,
% 25.49/25.73      (((k4_xboole_0 @ sk_A @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['437', '440', '441', '442'])).
% 25.49/25.73  thf('444', plain,
% 25.49/25.73      (((sk_B) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 25.49/25.73      inference('demod', [status(thm)], ['390', '443'])).
% 25.49/25.73  thf('445', plain,
% 25.49/25.73      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.73      inference('sup+', [status(thm)], ['384', '385'])).
% 25.49/25.73  thf('446', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('447', plain,
% 25.49/25.73      (((k2_xboole_0 @ sk_B @ sk_A)
% 25.49/25.73         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_A)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['445', '446'])).
% 25.49/25.73  thf('448', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 25.49/25.73      inference('sup+', [status(thm)], ['444', '447'])).
% 25.49/25.73  thf('449', plain,
% 25.49/25.73      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_A)) = (sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['389', '448'])).
% 25.49/25.73  thf('450', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('451', plain,
% 25.49/25.73      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B)
% 25.49/25.73         = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B))),
% 25.49/25.73      inference('sup+', [status(thm)], ['449', '450'])).
% 25.49/25.73  thf('452', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 25.49/25.73           = (k4_xboole_0 @ sk_A @ X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['438', '439'])).
% 25.49/25.73  thf('453', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)
% 25.49/25.73           = (X1))),
% 25.49/25.73      inference('sup+', [status(thm)], ['72', '73'])).
% 25.49/25.73  thf('454', plain,
% 25.49/25.73      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B) = (sk_B))),
% 25.49/25.73      inference('sup+', [status(thm)], ['452', '453'])).
% 25.49/25.73  thf('455', plain,
% 25.49/25.73      (((sk_B) = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['451', '454'])).
% 25.49/25.73  thf('456', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 25.49/25.73           = (k5_xboole_0 @ X2 @ 
% 25.49/25.73              (k5_xboole_0 @ X1 @ 
% 25.49/25.73               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['361', '362'])).
% 25.49/25.73  thf('457', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B) @ 
% 25.49/25.73           X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.73              (k5_xboole_0 @ sk_B @ 
% 25.49/25.73               (k5_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ X0)))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['455', '456'])).
% 25.49/25.73  thf('458', plain,
% 25.49/25.73      (((sk_B) = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['451', '454'])).
% 25.49/25.73  thf('459', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ X14 @ 
% 25.49/25.73              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.73      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.73  thf('460', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ sk_B @ X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.73              (k3_xboole_0 @ sk_B @ X0)))),
% 25.49/25.73      inference('demod', [status(thm)], ['457', '458', '459'])).
% 25.49/25.73  thf('461', plain,
% 25.49/25.73      (((k4_xboole_0 @ sk_A @ sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 25.49/25.73      inference('sup+', [status(thm)], ['384', '385'])).
% 25.49/25.73  thf('462', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ sk_B @ X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.73              (k3_xboole_0 @ sk_B @ X0)))),
% 25.49/25.73      inference('demod', [status(thm)], ['457', '458', '459'])).
% 25.49/25.73  thf('463', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('464', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['2', '3'])).
% 25.49/25.73  thf('465', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 25.49/25.73           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 25.49/25.73           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['463', '464'])).
% 25.49/25.73  thf('466', plain,
% 25.49/25.73      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 25.49/25.73      inference('demod', [status(thm)], ['433', '434'])).
% 25.49/25.73  thf('467', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ X14 @ 
% 25.49/25.73              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.73      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.73  thf('468', plain,
% 25.49/25.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.73           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.73  thf('469', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ 
% 25.49/25.73              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['467', '468'])).
% 25.49/25.73  thf('470', plain,
% 25.49/25.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.73           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.73  thf('471', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ 
% 25.49/25.73              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 25.49/25.73      inference('demod', [status(thm)], ['469', '470'])).
% 25.49/25.73  thf('472', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)) @ 
% 25.49/25.73           X0)
% 25.49/25.73           = (k5_xboole_0 @ sk_A @ 
% 25.49/25.73              (k5_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 25.49/25.73               (k5_xboole_0 @ sk_B @ X0))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['466', '471'])).
% 25.49/25.73  thf('473', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 25.49/25.73           = (k4_xboole_0 @ sk_A @ X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['438', '439'])).
% 25.49/25.73  thf('474', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['86', '87'])).
% 25.49/25.73  thf('475', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 25.49/25.73      inference('sup-', [status(thm)], ['22', '23'])).
% 25.49/25.73  thf('476', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ X0)
% 25.49/25.73           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ X0)))),
% 25.49/25.73      inference('demod', [status(thm)], ['472', '473', '474', '475'])).
% 25.49/25.73  thf('477', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['86', '87'])).
% 25.49/25.73  thf('478', plain,
% 25.49/25.73      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['374', '375'])).
% 25.49/25.73  thf('479', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.73      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.73  thf('480', plain, (((k2_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 25.49/25.73      inference('sup+', [status(thm)], ['478', '479'])).
% 25.49/25.73  thf('481', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 25.49/25.73      inference('demod', [status(thm)], ['378', '379', '380', '381'])).
% 25.49/25.73  thf('482', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['82', '83'])).
% 25.49/25.73  thf('483', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ X0)
% 25.49/25.73           = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['481', '482'])).
% 25.49/25.73  thf('484', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ 
% 25.49/25.73              (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ X1)))),
% 25.49/25.73      inference('demod', [status(thm)],
% 25.49/25.73                ['43', '386', '460', '461', '462', '465', '476', '477', '480', 
% 25.49/25.73                 '483'])).
% 25.49/25.73  thf('485', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['20', '484'])).
% 25.49/25.73  thf('486', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['16', '19'])).
% 25.49/25.73  thf('487', plain,
% 25.49/25.73      (![X0 : $i]: ((X0) = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_A) @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['485', '486'])).
% 25.49/25.73  thf('488', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_A) @ X0)
% 25.49/25.73           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['15', '487'])).
% 25.49/25.73  thf('489', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 25.49/25.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['396', '397'])).
% 25.49/25.73  thf('490', plain,
% 25.49/25.73      (![X2 : $i, X3 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X2 @ X3)
% 25.49/25.73           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 25.49/25.73  thf('491', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['489', '490'])).
% 25.49/25.73  thf('492', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ X14 @ 
% 25.49/25.73              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.73      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.73  thf('493', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 25.49/25.73              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['491', '492'])).
% 25.49/25.73  thf('494', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 25.49/25.73           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['177', '178'])).
% 25.49/25.73  thf('495', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 25.49/25.73              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))))),
% 25.49/25.73      inference('demod', [status(thm)], ['493', '494'])).
% 25.49/25.73  thf('496', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 25.49/25.73           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 25.49/25.73           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['463', '464'])).
% 25.49/25.73  thf('497', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.73      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.73  thf('498', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['495', '496', '497'])).
% 25.49/25.73  thf('499', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 25.49/25.73           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['59', '60'])).
% 25.49/25.73  thf('500', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))
% 25.49/25.73           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['498', '499'])).
% 25.49/25.73  thf('501', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['495', '496', '497'])).
% 25.49/25.73  thf('502', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.73      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.73  thf('503', plain,
% 25.49/25.73      (![X0 : $i]: ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['501', '502'])).
% 25.49/25.73  thf('504', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 25.49/25.73           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('demod', [status(thm)], ['328', '329'])).
% 25.49/25.73  thf('505', plain,
% 25.49/25.73      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['503', '504'])).
% 25.49/25.73  thf('506', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))
% 25.49/25.73           = (X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['500', '505'])).
% 25.49/25.73  thf('507', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['495', '496', '497'])).
% 25.49/25.73  thf('508', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ 
% 25.49/25.73           (k3_xboole_0 @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 25.49/25.73           X2) = (X2))),
% 25.49/25.73      inference('sup+', [status(thm)], ['321', '322'])).
% 25.49/25.73  thf('509', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ 
% 25.49/25.73           (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)) @ 
% 25.49/25.73           X1) = (X1))),
% 25.49/25.73      inference('sup+', [status(thm)], ['507', '508'])).
% 25.49/25.73  thf('510', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ X14 @ 
% 25.49/25.73              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.73      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.73  thf('511', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ 
% 25.49/25.73           (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)) @ 
% 25.49/25.73           X0)
% 25.49/25.73           = (k5_xboole_0 @ 
% 25.49/25.73              (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)) @ 
% 25.49/25.73              (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['509', '510'])).
% 25.49/25.73  thf('512', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.73  thf('513', plain,
% 25.49/25.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 25.49/25.73           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t91_xboole_1])).
% 25.49/25.73  thf('514', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('demod', [status(thm)], ['132', '133'])).
% 25.49/25.73  thf('515', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('516', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['82', '83'])).
% 25.49/25.73  thf('517', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ 
% 25.49/25.73           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['515', '516'])).
% 25.49/25.73  thf('518', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['16', '19'])).
% 25.49/25.73  thf('519', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ 
% 25.49/25.73           (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)],
% 25.49/25.73                ['511', '512', '513', '514', '517', '518'])).
% 25.49/25.73  thf('520', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ 
% 25.49/25.73           (k5_xboole_0 @ 
% 25.49/25.73            (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)) @ 
% 25.49/25.73            X0))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['506', '519'])).
% 25.49/25.73  thf('521', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))
% 25.49/25.73           = (X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['500', '505'])).
% 25.49/25.73  thf('522', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['520', '521'])).
% 25.49/25.73  thf('523', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 25.49/25.73           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['59', '60'])).
% 25.49/25.73  thf('524', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))
% 25.49/25.73           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['522', '523'])).
% 25.49/25.73  thf('525', plain,
% 25.49/25.73      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['503', '504'])).
% 25.49/25.73  thf('526', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))
% 25.49/25.73           = (X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['524', '525'])).
% 25.49/25.73  thf('527', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('528', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['526', '527'])).
% 25.49/25.73  thf('529', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['495', '496', '497'])).
% 25.49/25.73  thf('530', plain,
% 25.49/25.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 25.49/25.73           = (k4_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10))),
% 25.49/25.73      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.49/25.73  thf('531', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))
% 25.49/25.73           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 25.49/25.73      inference('sup+', [status(thm)], ['529', '530'])).
% 25.49/25.73  thf('532', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 25.49/25.73      inference('sup-', [status(thm)], ['17', '18'])).
% 25.49/25.73  thf('533', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ X1)
% 25.49/25.73           = (X1))),
% 25.49/25.73      inference('sup+', [status(thm)], ['531', '532'])).
% 25.49/25.73  thf('534', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['528', '533'])).
% 25.49/25.73  thf('535', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 25.49/25.73              (k2_xboole_0 @ X14 @ X15)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t95_xboole_1])).
% 25.49/25.73  thf('536', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ 
% 25.49/25.73              (k2_xboole_0 @ X14 @ X15)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t95_xboole_1])).
% 25.49/25.73  thf('537', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 25.49/25.73              (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['535', '536'])).
% 25.49/25.73  thf('538', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 25.49/25.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.49/25.73  thf('539', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 25.49/25.73           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 25.49/25.73              (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 25.49/25.73      inference('demod', [status(thm)], ['537', '538'])).
% 25.49/25.73  thf('540', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 25.49/25.73           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['82', '83'])).
% 25.49/25.73  thf('541', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 25.49/25.73           (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ 
% 25.49/25.73              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['539', '540'])).
% 25.49/25.73  thf('542', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ 
% 25.49/25.73           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)) @ 
% 25.49/25.73           (k2_xboole_0 @ X0 @ 
% 25.49/25.73            (k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0)))
% 25.49/25.73           = (k5_xboole_0 @ X0 @ 
% 25.49/25.73              (k3_xboole_0 @ 
% 25.49/25.73               (k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0) @ 
% 25.49/25.73               (k5_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0))))),
% 25.49/25.73      inference('sup+', [status(thm)], ['534', '541'])).
% 25.49/25.73  thf('543', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))
% 25.49/25.73           = (X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['524', '525'])).
% 25.49/25.73  thf('544', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ X1)
% 25.49/25.73           = (X1))),
% 25.49/25.73      inference('sup+', [status(thm)], ['531', '532'])).
% 25.49/25.73  thf('545', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ X1)
% 25.49/25.73           = (X1))),
% 25.49/25.73      inference('sup+', [status(thm)], ['531', '532'])).
% 25.49/25.73  thf('546', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((X0)
% 25.49/25.73           = (k5_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['528', '533'])).
% 25.49/25.73  thf('547', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i]:
% 25.49/25.73         ((k4_xboole_0 @ X0 @ X1)
% 25.49/25.73           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['44', '45'])).
% 25.49/25.73  thf('548', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))
% 25.49/25.73           = (k4_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)],
% 25.49/25.73                ['542', '543', '544', '545', '546', '547'])).
% 25.49/25.73  thf('549', plain,
% 25.49/25.73      (![X14 : $i, X15 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X14 @ X15)
% 25.49/25.73           = (k5_xboole_0 @ X14 @ 
% 25.49/25.73              (k5_xboole_0 @ X15 @ (k2_xboole_0 @ X14 @ X15))))),
% 25.49/25.73      inference('demod', [status(thm)], ['52', '53'])).
% 25.49/25.73  thf('550', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ X0 @ X0)
% 25.49/25.73           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 25.49/25.73      inference('sup+', [status(thm)], ['548', '549'])).
% 25.49/25.73  thf('551', plain,
% 25.49/25.73      (![X16 : $i, X17 : $i]:
% 25.49/25.73         ((k2_xboole_0 @ X16 @ X17)
% 25.49/25.73           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 25.49/25.73      inference('cnf', [status(esa)], [t98_xboole_1])).
% 25.49/25.73  thf('552', plain,
% 25.49/25.73      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 25.49/25.73      inference('demod', [status(thm)], ['550', '551'])).
% 25.49/25.73  thf('553', plain, (((k2_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 25.49/25.73      inference('sup+', [status(thm)], ['478', '479'])).
% 25.49/25.73  thf('554', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ sk_A @ X0)
% 25.49/25.73           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0)))),
% 25.49/25.73      inference('demod', [status(thm)], ['488', '552', '553'])).
% 25.49/25.73  thf('555', plain,
% 25.49/25.73      (![X0 : $i]:
% 25.49/25.73         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 25.49/25.73           = (k4_xboole_0 @ sk_A @ X0))),
% 25.49/25.73      inference('sup+', [status(thm)], ['438', '439'])).
% 25.49/25.73  thf('556', plain,
% 25.49/25.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.49/25.73         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1)),
% 25.49/25.73      inference('sup+', [status(thm)], ['181', '182'])).
% 25.49/25.73  thf('557', plain,
% 25.49/25.73      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 25.49/25.73      inference('sup+', [status(thm)], ['555', '556'])).
% 25.49/25.73  thf('558', plain,
% 25.49/25.73      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 25.49/25.73      inference('sup+', [status(thm)], ['554', '557'])).
% 25.49/25.73  thf('559', plain, ($false), inference('demod', [status(thm)], ['0', '558'])).
% 25.49/25.73  
% 25.49/25.73  % SZS output end Refutation
% 25.49/25.73  
% 25.49/25.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
