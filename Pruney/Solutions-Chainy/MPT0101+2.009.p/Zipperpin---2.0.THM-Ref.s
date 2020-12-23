%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LcDCVhSqlk

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:55 EST 2020

% Result     : Theorem 41.52s
% Output     : Refutation 41.52s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 804 expanded)
%              Number of leaves         :   17 ( 286 expanded)
%              Depth                    :   20
%              Number of atoms          : 1730 (7443 expanded)
%              Number of equality atoms :  158 ( 708 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('78',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','84','85'])).

thf('87',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','18','19','20'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('98',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['61','101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['40','104','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','108'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','111'])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('119',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('129',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('132',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('133',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('134',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['131','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['131','138'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['127','130','139','140'])).

thf('142',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('147',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','143'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','144','145','146','147','148','149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('153',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','151','152'])).

thf('154',plain,(
    $false ),
    inference(simplify,[status(thm)],['153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LcDCVhSqlk
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 41.52/41.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 41.52/41.71  % Solved by: fo/fo7.sh
% 41.52/41.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 41.52/41.71  % done 12300 iterations in 41.250s
% 41.52/41.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 41.52/41.71  % SZS output start Refutation
% 41.52/41.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 41.52/41.71  thf(sk_B_type, type, sk_B: $i).
% 41.52/41.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 41.52/41.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 41.52/41.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 41.52/41.71  thf(sk_A_type, type, sk_A: $i).
% 41.52/41.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 41.52/41.71  thf(t94_xboole_1, conjecture,
% 41.52/41.71    (![A:$i,B:$i]:
% 41.52/41.71     ( ( k2_xboole_0 @ A @ B ) =
% 41.52/41.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 41.52/41.71  thf(zf_stmt_0, negated_conjecture,
% 41.52/41.71    (~( ![A:$i,B:$i]:
% 41.52/41.71        ( ( k2_xboole_0 @ A @ B ) =
% 41.52/41.71          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 41.52/41.71    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 41.52/41.71  thf('0', plain,
% 41.52/41.71      (((k2_xboole_0 @ sk_A @ sk_B)
% 41.52/41.71         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 41.52/41.71             (k3_xboole_0 @ sk_A @ sk_B)))),
% 41.52/41.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 41.52/41.71  thf(d6_xboole_0, axiom,
% 41.52/41.71    (![A:$i,B:$i]:
% 41.52/41.71     ( ( k5_xboole_0 @ A @ B ) =
% 41.52/41.71       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 41.52/41.71  thf('1', plain,
% 41.52/41.71      (![X4 : $i, X5 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ X4 @ X5)
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 41.52/41.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 41.52/41.71  thf(t48_xboole_1, axiom,
% 41.52/41.71    (![A:$i,B:$i]:
% 41.52/41.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 41.52/41.71  thf('2', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf(t41_xboole_1, axiom,
% 41.52/41.71    (![A:$i,B:$i,C:$i]:
% 41.52/41.71     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 41.52/41.71       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 41.52/41.71  thf('3', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('4', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['2', '3'])).
% 41.52/41.71  thf(t79_xboole_1, axiom,
% 41.52/41.71    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 41.52/41.71  thf('5', plain,
% 41.52/41.71      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 41.52/41.71      inference('cnf', [status(esa)], [t79_xboole_1])).
% 41.52/41.71  thf(t83_xboole_1, axiom,
% 41.52/41.71    (![A:$i,B:$i]:
% 41.52/41.71     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 41.52/41.71  thf('6', plain,
% 41.52/41.71      (![X15 : $i, X16 : $i]:
% 41.52/41.71         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 41.52/41.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 41.52/41.71  thf('7', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup-', [status(thm)], ['5', '6'])).
% 41.52/41.71  thf('8', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('9', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('10', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('11', plain,
% 41.52/41.71      (![X4 : $i, X5 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ X4 @ X5)
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 41.52/41.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 41.52/41.71  thf('12', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 41.52/41.71              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 41.52/41.71      inference('sup+', [status(thm)], ['10', '11'])).
% 41.52/41.71  thf('13', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 41.52/41.71              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 41.52/41.71      inference('sup+', [status(thm)], ['9', '12'])).
% 41.52/41.71  thf('14', plain,
% 41.52/41.71      (![X4 : $i, X5 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ X4 @ X5)
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 41.52/41.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 41.52/41.71  thf(commutativity_k2_xboole_0, axiom,
% 41.52/41.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 41.52/41.71  thf('15', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('16', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k5_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['14', '15'])).
% 41.52/41.71  thf('17', plain,
% 41.52/41.71      (![X4 : $i, X5 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ X4 @ X5)
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 41.52/41.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 41.52/41.71  thf('18', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['16', '17'])).
% 41.52/41.71  thf(t39_xboole_1, axiom,
% 41.52/41.71    (![A:$i,B:$i]:
% 41.52/41.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 41.52/41.71  thf('19', plain,
% 41.52/41.71      (![X6 : $i, X7 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 41.52/41.71           = (k2_xboole_0 @ X6 @ X7))),
% 41.52/41.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 41.52/41.71  thf('20', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('21', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['13', '18', '19', '20'])).
% 41.52/41.71  thf('22', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 41.52/41.71           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 41.52/41.71           = (k2_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 41.52/41.71              (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['4', '21'])).
% 41.52/41.71  thf('23', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['2', '3'])).
% 41.52/41.71  thf('24', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['16', '17'])).
% 41.52/41.71  thf('25', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('26', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 41.52/41.71           (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 41.52/41.71              (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 41.52/41.71  thf(commutativity_k3_xboole_0, axiom,
% 41.52/41.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 41.52/41.71  thf('27', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf('28', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('29', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('30', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('31', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('32', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 41.52/41.71           = (k4_xboole_0 @ X2 @ 
% 41.52/41.71              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 41.52/41.71      inference('sup+', [status(thm)], ['30', '31'])).
% 41.52/41.71  thf('33', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('34', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 41.52/41.71           = (k4_xboole_0 @ X2 @ 
% 41.52/41.71              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 41.52/41.71      inference('demod', [status(thm)], ['32', '33'])).
% 41.52/41.71  thf('35', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 41.52/41.71           = (k4_xboole_0 @ X2 @ 
% 41.52/41.71              (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 41.52/41.71      inference('sup+', [status(thm)], ['29', '34'])).
% 41.52/41.71  thf('36', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('37', plain,
% 41.52/41.71      (![X6 : $i, X7 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 41.52/41.71           = (k2_xboole_0 @ X6 @ X7))),
% 41.52/41.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 41.52/41.71  thf('38', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 41.52/41.71           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['36', '37'])).
% 41.52/41.71  thf('39', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 41.52/41.71           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 41.52/41.71      inference('demod', [status(thm)], ['35', '38'])).
% 41.52/41.71  thf('40', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 41.52/41.71      inference('sup+', [status(thm)], ['28', '39'])).
% 41.52/41.71  thf('41', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('42', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('43', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['41', '42'])).
% 41.52/41.71  thf('44', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('45', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X1 @ X0)
% 41.52/41.71           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['43', '44'])).
% 41.52/41.71  thf('46', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf('47', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['45', '46'])).
% 41.52/41.71  thf('48', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('49', plain,
% 41.52/41.71      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 41.52/41.71      inference('cnf', [status(esa)], [t79_xboole_1])).
% 41.52/41.71  thf('50', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['48', '49'])).
% 41.52/41.71  thf('51', plain,
% 41.52/41.71      (![X15 : $i, X16 : $i]:
% 41.52/41.71         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 41.52/41.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 41.52/41.71  thf('52', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup-', [status(thm)], ['50', '51'])).
% 41.52/41.71  thf('53', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('54', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['52', '53'])).
% 41.52/41.71  thf('55', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('56', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))))),
% 41.52/41.71      inference('sup+', [status(thm)], ['54', '55'])).
% 41.52/41.71  thf('57', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('58', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X1 @ X0)
% 41.52/41.71           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))))),
% 41.52/41.71      inference('demod', [status(thm)], ['56', '57'])).
% 41.52/41.71  thf('59', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 41.52/41.71           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X1)) @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['47', '58'])).
% 41.52/41.71  thf('60', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['45', '46'])).
% 41.52/41.71  thf('61', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X1 @ X0)
% 41.52/41.71           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X1)) @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['59', '60'])).
% 41.52/41.71  thf('62', plain,
% 41.52/41.71      (![X4 : $i, X5 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ X4 @ X5)
% 41.52/41.71           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 41.52/41.71      inference('cnf', [status(esa)], [d6_xboole_0])).
% 41.52/41.71  thf('63', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('64', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['62', '63'])).
% 41.52/41.71  thf('65', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('66', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['64', '65'])).
% 41.52/41.71  thf('67', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup-', [status(thm)], ['5', '6'])).
% 41.52/41.71  thf('68', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('69', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['67', '68'])).
% 41.52/41.71  thf('70', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf('71', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['69', '70'])).
% 41.52/41.71  thf('72', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('73', plain,
% 41.52/41.71      (![X6 : $i, X7 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 41.52/41.71           = (k2_xboole_0 @ X6 @ X7))),
% 41.52/41.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 41.52/41.71  thf('74', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['71', '72', '73'])).
% 41.52/41.71  thf('75', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))
% 41.52/41.71           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['66', '74'])).
% 41.52/41.71  thf('76', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('77', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['64', '65'])).
% 41.52/41.71  thf('78', plain,
% 41.52/41.71      (![X6 : $i, X7 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 41.52/41.71           = (k2_xboole_0 @ X6 @ X7))),
% 41.52/41.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 41.52/41.71  thf('79', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['77', '78'])).
% 41.52/41.71  thf('80', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf(t93_xboole_1, axiom,
% 41.52/41.71    (![A:$i,B:$i]:
% 41.52/41.71     ( ( k2_xboole_0 @ A @ B ) =
% 41.52/41.71       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 41.52/41.71  thf('81', plain,
% 41.52/41.71      (![X18 : $i, X19 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X18 @ X19)
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 41.52/41.71              (k3_xboole_0 @ X18 @ X19)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t93_xboole_1])).
% 41.52/41.71  thf('82', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ X1)
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['80', '81'])).
% 41.52/41.71  thf('83', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('84', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ X0)
% 41.52/41.71           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['79', '82', '83'])).
% 41.52/41.71  thf('85', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('86', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X0 @ X0)
% 41.52/41.71           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['75', '76', '84', '85'])).
% 41.52/41.71  thf('87', plain,
% 41.52/41.71      (![X18 : $i, X19 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X18 @ X19)
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 41.52/41.71              (k3_xboole_0 @ X18 @ X19)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t93_xboole_1])).
% 41.52/41.71  thf('88', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k2_xboole_0 @ 
% 41.52/41.71              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0)) @ 
% 41.52/41.71              (k4_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['86', '87'])).
% 41.52/41.71  thf('89', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ X1)
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['80', '81'])).
% 41.52/41.71  thf('90', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['64', '65'])).
% 41.52/41.71  thf('91', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['13', '18', '19', '20'])).
% 41.52/41.71  thf('92', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 41.52/41.71           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['90', '91'])).
% 41.52/41.71  thf('93', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['64', '65'])).
% 41.52/41.71  thf('94', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ X1)
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['80', '81'])).
% 41.52/41.71  thf('95', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k2_xboole_0 @ X0 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['92', '93', '94'])).
% 41.52/41.71  thf('96', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ X0)
% 41.52/41.71           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['88', '89', '95'])).
% 41.52/41.71  thf('97', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('98', plain,
% 41.52/41.71      (![X6 : $i, X7 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 41.52/41.71           = (k2_xboole_0 @ X6 @ X7))),
% 41.52/41.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 41.52/41.71  thf('99', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1))),
% 41.52/41.71      inference('sup+', [status(thm)], ['97', '98'])).
% 41.52/41.71  thf('100', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('101', plain,
% 41.52/41.71      (![X0 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ X0)
% 41.52/41.71           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['96', '99', '100'])).
% 41.52/41.71  thf('102', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X1 @ X0)
% 41.52/41.71           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['61', '101'])).
% 41.52/41.71  thf('103', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf('104', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['102', '103'])).
% 41.52/41.71  thf('105', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('106', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['2', '3'])).
% 41.52/41.71  thf('107', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 41.52/41.71      inference('sup+', [status(thm)], ['105', '106'])).
% 41.52/41.71  thf('108', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 41.52/41.71           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 41.52/41.71      inference('demod', [status(thm)], ['40', '104', '107'])).
% 41.52/41.71  thf('109', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 41.52/41.71           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 41.52/41.71      inference('sup+', [status(thm)], ['27', '108'])).
% 41.52/41.71  thf('110', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 41.52/41.71           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 41.52/41.71      inference('sup+', [status(thm)], ['27', '108'])).
% 41.52/41.71  thf('111', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 41.52/41.71           (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 41.52/41.71           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 41.52/41.71              (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 41.52/41.71      inference('demod', [status(thm)], ['26', '109', '110'])).
% 41.52/41.71  thf('112', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ 
% 41.52/41.71           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 41.52/41.71           (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))
% 41.52/41.71           = (k2_xboole_0 @ 
% 41.52/41.71              (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 41.52/41.71              (k5_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['1', '111'])).
% 41.52/41.71  thf('113', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('114', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf('115', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['7', '8'])).
% 41.52/41.71  thf('116', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 41.52/41.71           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 41.52/41.71      inference('demod', [status(thm)], ['35', '38'])).
% 41.52/41.71  thf('117', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['115', '116'])).
% 41.52/41.71  thf('118', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('119', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('120', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 41.52/41.71           = (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup-', [status(thm)], ['5', '6'])).
% 41.52/41.71  thf('121', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['119', '120'])).
% 41.52/41.71  thf('122', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('123', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['121', '122'])).
% 41.52/41.71  thf('124', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('125', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['121', '122'])).
% 41.52/41.71  thf('126', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 41.52/41.71           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 41.52/41.71           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['124', '125'])).
% 41.52/41.71  thf('127', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 41.52/41.71           (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 41.52/41.71            (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))
% 41.52/41.71           = (k3_xboole_0 @ 
% 41.52/41.71              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)) @ 
% 41.52/41.71              X2))),
% 41.52/41.71      inference('sup+', [status(thm)], ['123', '126'])).
% 41.52/41.71  thf('128', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['121', '122'])).
% 41.52/41.71  thf('129', plain,
% 41.52/41.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 41.52/41.71           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 41.52/41.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 41.52/41.71  thf('130', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 41.52/41.71           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 41.52/41.71              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['128', '129'])).
% 41.52/41.71  thf('131', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf('132', plain,
% 41.52/41.71      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 41.52/41.71  thf('133', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('134', plain,
% 41.52/41.71      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 41.52/41.71      inference('cnf', [status(esa)], [t79_xboole_1])).
% 41.52/41.71  thf('135', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['133', '134'])).
% 41.52/41.71  thf('136', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('sup+', [status(thm)], ['132', '135'])).
% 41.52/41.71  thf('137', plain,
% 41.52/41.71      (![X15 : $i, X16 : $i]:
% 41.52/41.71         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 41.52/41.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 41.52/41.71  thf('138', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('sup-', [status(thm)], ['136', '137'])).
% 41.52/41.71  thf('139', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('sup+', [status(thm)], ['131', '138'])).
% 41.52/41.71  thf('140', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('sup+', [status(thm)], ['131', '138'])).
% 41.52/41.71  thf('141', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 41.52/41.71      inference('demod', [status(thm)], ['127', '130', '139', '140'])).
% 41.52/41.71  thf('142', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('143', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)], ['117', '118', '141', '142'])).
% 41.52/41.71  thf('144', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['114', '143'])).
% 41.52/41.71  thf('145', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k5_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['14', '15'])).
% 41.52/41.71  thf('146', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['16', '17'])).
% 41.52/41.71  thf('147', plain,
% 41.52/41.71      (![X11 : $i, X12 : $i]:
% 41.52/41.71         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 41.52/41.71           = (k3_xboole_0 @ X11 @ X12))),
% 41.52/41.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 41.52/41.71  thf('148', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 41.52/41.71           = (k3_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('sup+', [status(thm)], ['114', '143'])).
% 41.52/41.71  thf('149', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('150', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k2_xboole_0 @ X0 @ X1)
% 41.52/41.71           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 41.52/41.71      inference('sup+', [status(thm)], ['80', '81'])).
% 41.52/41.71  thf('151', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]:
% 41.52/41.71         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 41.52/41.71           = (k2_xboole_0 @ X1 @ X0))),
% 41.52/41.71      inference('demod', [status(thm)],
% 41.52/41.71                ['112', '113', '144', '145', '146', '147', '148', '149', '150'])).
% 41.52/41.71  thf('152', plain,
% 41.52/41.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 41.52/41.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 41.52/41.71  thf('153', plain,
% 41.52/41.71      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 41.52/41.71      inference('demod', [status(thm)], ['0', '151', '152'])).
% 41.52/41.71  thf('154', plain, ($false), inference('simplify', [status(thm)], ['153'])).
% 41.52/41.71  
% 41.52/41.71  % SZS output end Refutation
% 41.52/41.71  
% 41.52/41.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
