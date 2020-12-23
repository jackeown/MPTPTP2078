%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jz293xiRsU

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:54 EST 2020

% Result     : Theorem 3.54s
% Output     : Refutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 324 expanded)
%              Number of leaves         :   14 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :  870 (3090 expanded)
%              Number of equality atoms :   85 ( 317 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t93_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','55'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','55'])).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','73','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jz293xiRsU
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.54/3.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.54/3.72  % Solved by: fo/fo7.sh
% 3.54/3.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.54/3.72  % done 1102 iterations in 3.265s
% 3.54/3.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.54/3.72  % SZS output start Refutation
% 3.54/3.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.54/3.72  thf(sk_A_type, type, sk_A: $i).
% 3.54/3.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.54/3.72  thf(sk_B_type, type, sk_B: $i).
% 3.54/3.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.54/3.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.54/3.72  thf(t93_xboole_1, conjecture,
% 3.54/3.72    (![A:$i,B:$i]:
% 3.54/3.72     ( ( k2_xboole_0 @ A @ B ) =
% 3.54/3.72       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.54/3.72  thf(zf_stmt_0, negated_conjecture,
% 3.54/3.72    (~( ![A:$i,B:$i]:
% 3.54/3.72        ( ( k2_xboole_0 @ A @ B ) =
% 3.54/3.72          ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 3.54/3.72    inference('cnf.neg', [status(esa)], [t93_xboole_1])).
% 3.54/3.72  thf('0', plain,
% 3.54/3.72      (((k2_xboole_0 @ sk_A @ sk_B)
% 3.54/3.72         != (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 3.54/3.72             (k3_xboole_0 @ sk_A @ sk_B)))),
% 3.54/3.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.54/3.72  thf(t48_xboole_1, axiom,
% 3.54/3.72    (![A:$i,B:$i]:
% 3.54/3.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.54/3.72  thf('1', plain,
% 3.54/3.72      (![X9 : $i, X10 : $i]:
% 3.54/3.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 3.54/3.72           = (k3_xboole_0 @ X9 @ X10))),
% 3.54/3.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.54/3.72  thf(t39_xboole_1, axiom,
% 3.54/3.72    (![A:$i,B:$i]:
% 3.54/3.72     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.54/3.72  thf('2', plain,
% 3.54/3.72      (![X4 : $i, X5 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 3.54/3.72           = (k2_xboole_0 @ X4 @ X5))),
% 3.54/3.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.54/3.72  thf('3', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 3.54/3.72      inference('sup+', [status(thm)], ['1', '2'])).
% 3.54/3.72  thf(commutativity_k2_xboole_0, axiom,
% 3.54/3.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.54/3.72  thf('4', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('5', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('6', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['3', '4', '5'])).
% 3.54/3.72  thf(d6_xboole_0, axiom,
% 3.54/3.72    (![A:$i,B:$i]:
% 3.54/3.72     ( ( k5_xboole_0 @ A @ B ) =
% 3.54/3.72       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.54/3.72  thf('7', plain,
% 3.54/3.72      (![X2 : $i, X3 : $i]:
% 3.54/3.72         ((k5_xboole_0 @ X2 @ X3)
% 3.54/3.72           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 3.54/3.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 3.54/3.72  thf(t4_xboole_1, axiom,
% 3.54/3.72    (![A:$i,B:$i,C:$i]:
% 3.54/3.72     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 3.54/3.72       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.54/3.72  thf('8', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('9', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('10', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 3.54/3.72           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['8', '9'])).
% 3.54/3.72  thf('11', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 3.54/3.72           (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 3.54/3.72           = (k2_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['7', '10'])).
% 3.54/3.72  thf('12', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 3.54/3.72           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 3.54/3.72           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['6', '11'])).
% 3.54/3.72  thf('13', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 3.54/3.72           (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 3.54/3.72           = (k2_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['7', '10'])).
% 3.54/3.72  thf('14', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('15', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['12', '13', '14'])).
% 3.54/3.72  thf('16', plain,
% 3.54/3.72      (![X2 : $i, X3 : $i]:
% 3.54/3.72         ((k5_xboole_0 @ X2 @ X3)
% 3.54/3.72           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 3.54/3.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 3.54/3.72  thf('17', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('18', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k5_xboole_0 @ X1 @ X0))),
% 3.54/3.72      inference('sup+', [status(thm)], ['16', '17'])).
% 3.54/3.72  thf('19', plain,
% 3.54/3.72      (![X2 : $i, X3 : $i]:
% 3.54/3.72         ((k5_xboole_0 @ X2 @ X3)
% 3.54/3.72           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 3.54/3.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 3.54/3.72  thf('20', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.54/3.72      inference('sup+', [status(thm)], ['18', '19'])).
% 3.54/3.72  thf('21', plain,
% 3.54/3.72      (![X2 : $i, X3 : $i]:
% 3.54/3.72         ((k5_xboole_0 @ X2 @ X3)
% 3.54/3.72           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 3.54/3.72      inference('cnf', [status(esa)], [d6_xboole_0])).
% 3.54/3.72  thf('22', plain,
% 3.54/3.72      (![X4 : $i, X5 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 3.54/3.72           = (k2_xboole_0 @ X4 @ X5))),
% 3.54/3.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.54/3.72  thf('23', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('24', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.54/3.72           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['22', '23'])).
% 3.54/3.72  thf('25', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('26', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 3.54/3.72           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 3.54/3.72      inference('demod', [status(thm)], ['24', '25'])).
% 3.54/3.72  thf('27', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['21', '26'])).
% 3.54/3.72  thf(t6_xboole_1, axiom,
% 3.54/3.72    (![A:$i,B:$i]:
% 3.54/3.72     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.54/3.72  thf('28', plain,
% 3.54/3.72      (![X14 : $i, X15 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15))
% 3.54/3.72           = (k2_xboole_0 @ X14 @ X15))),
% 3.54/3.72      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.54/3.72  thf('29', plain,
% 3.54/3.72      (![X4 : $i, X5 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 3.54/3.72           = (k2_xboole_0 @ X4 @ X5))),
% 3.54/3.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.54/3.72  thf('30', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('31', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 3.54/3.72           = (k2_xboole_0 @ X2 @ 
% 3.54/3.72              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))))),
% 3.54/3.72      inference('sup+', [status(thm)], ['29', '30'])).
% 3.54/3.72  thf('32', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('33', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X2 @ 
% 3.54/3.72              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))))),
% 3.54/3.72      inference('demod', [status(thm)], ['31', '32'])).
% 3.54/3.72  thf('34', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf(t41_xboole_1, axiom,
% 3.54/3.72    (![A:$i,B:$i,C:$i]:
% 3.54/3.72     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.54/3.72       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.54/3.72  thf('35', plain,
% 3.54/3.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.54/3.72         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 3.54/3.72           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.54/3.72  thf('36', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 3.54/3.72           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['34', '35'])).
% 3.54/3.72  thf('37', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X2 @ 
% 3.54/3.72              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))))),
% 3.54/3.72      inference('demod', [status(thm)], ['33', '36'])).
% 3.54/3.72  thf('38', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['28', '37'])).
% 3.54/3.72  thf('39', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('40', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('41', plain,
% 3.54/3.72      (![X14 : $i, X15 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15))
% 3.54/3.72           = (k2_xboole_0 @ X14 @ X15))),
% 3.54/3.72      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.54/3.72  thf('42', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('sup+', [status(thm)], ['40', '41'])).
% 3.54/3.72  thf('43', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('sup+', [status(thm)], ['40', '41'])).
% 3.54/3.72  thf('44', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))),
% 3.54/3.72      inference('sup+', [status(thm)], ['42', '43'])).
% 3.54/3.72  thf('45', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('46', plain,
% 3.54/3.72      (![X14 : $i, X15 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15))
% 3.54/3.72           = (k2_xboole_0 @ X14 @ X15))),
% 3.54/3.72      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.54/3.72  thf('47', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('48', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 3.54/3.72      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 3.54/3.72  thf('49', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('sup+', [status(thm)], ['40', '41'])).
% 3.54/3.72  thf('50', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ X1)
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 3.54/3.72      inference('demod', [status(thm)], ['48', '49'])).
% 3.54/3.72  thf('51', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ X1)
% 3.54/3.72           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0))),
% 3.54/3.72      inference('sup+', [status(thm)], ['39', '50'])).
% 3.54/3.72  thf('52', plain,
% 3.54/3.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 3.54/3.72           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 3.54/3.72      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.54/3.72  thf('53', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ X1)
% 3.54/3.72           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['51', '52'])).
% 3.54/3.72  thf('54', plain,
% 3.54/3.72      (![X4 : $i, X5 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 3.54/3.72           = (k2_xboole_0 @ X4 @ X5))),
% 3.54/3.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.54/3.72  thf('55', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X1 @ X0)
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['38', '53', '54'])).
% 3.54/3.72  thf('56', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['27', '55'])).
% 3.54/3.72  thf('57', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ X1)
% 3.54/3.72           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['51', '52'])).
% 3.54/3.72  thf('58', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 3.54/3.72      inference('sup+', [status(thm)], ['56', '57'])).
% 3.54/3.72  thf('59', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 3.54/3.72           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['8', '9'])).
% 3.54/3.72  thf('60', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('61', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 3.54/3.72           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['59', '60'])).
% 3.54/3.72  thf('62', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ X1)
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 3.54/3.72      inference('demod', [status(thm)], ['48', '49'])).
% 3.54/3.72  thf('63', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['27', '55'])).
% 3.54/3.72  thf('64', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X1 @ X0)
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['58', '61', '62', '63'])).
% 3.54/3.72  thf('65', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.54/3.72      inference('sup+', [status(thm)], ['18', '19'])).
% 3.54/3.72  thf('66', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.54/3.72      inference('sup+', [status(thm)], ['18', '19'])).
% 3.54/3.72  thf('67', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['27', '55'])).
% 3.54/3.72  thf('68', plain,
% 3.54/3.72      (![X14 : $i, X15 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15))
% 3.54/3.72           = (k2_xboole_0 @ X14 @ X15))),
% 3.54/3.72      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.54/3.72  thf('69', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('sup+', [status(thm)], ['67', '68'])).
% 3.54/3.72  thf('70', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 3.54/3.72           = (k2_xboole_0 @ X1 @ X0))),
% 3.54/3.72      inference('sup+', [status(thm)], ['66', '69'])).
% 3.54/3.72  thf('71', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X1 @ X0)
% 3.54/3.72           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['64', '65', '70'])).
% 3.54/3.72  thf('72', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ X1)
% 3.54/3.72           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('sup+', [status(thm)], ['20', '71'])).
% 3.54/3.72  thf('73', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]:
% 3.54/3.72         ((k2_xboole_0 @ X0 @ X1)
% 3.54/3.72           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.54/3.72      inference('demod', [status(thm)], ['15', '72'])).
% 3.54/3.72  thf('74', plain,
% 3.54/3.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.54/3.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.54/3.72  thf('75', plain,
% 3.54/3.72      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 3.54/3.72      inference('demod', [status(thm)], ['0', '73', '74'])).
% 3.54/3.72  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 3.54/3.72  
% 3.54/3.72  % SZS output end Refutation
% 3.54/3.72  
% 3.54/3.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
