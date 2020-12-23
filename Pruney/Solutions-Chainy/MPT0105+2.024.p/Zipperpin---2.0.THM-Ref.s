%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ijoiLnSJU

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:08 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  612 ( 962 expanded)
%              Number of equality atoms :   69 ( 113 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X16 ) @ X17 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X17 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','48'])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6ijoiLnSJU
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.74  % Solved by: fo/fo7.sh
% 0.56/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.74  % done 545 iterations in 0.271s
% 0.56/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.74  % SZS output start Refutation
% 0.56/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.56/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(t98_xboole_1, conjecture,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.56/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.74    (~( ![A:$i,B:$i]:
% 0.56/0.74        ( ( k2_xboole_0 @ A @ B ) =
% 0.56/0.74          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.56/0.74    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.56/0.74  thf('0', plain,
% 0.56/0.74      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.56/0.74         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(t48_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.56/0.74  thf('1', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.56/0.74           = (k3_xboole_0 @ X10 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.74  thf(t4_boole, axiom,
% 0.56/0.74    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.56/0.74  thf('2', plain,
% 0.56/0.74      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t4_boole])).
% 0.56/0.74  thf('3', plain,
% 0.56/0.74      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['1', '2'])).
% 0.56/0.74  thf(t94_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k2_xboole_0 @ A @ B ) =
% 0.56/0.74       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.56/0.74  thf('4', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X22 @ X23)
% 0.56/0.74           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.56/0.74              (k3_xboole_0 @ X22 @ X23)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.56/0.74  thf(t91_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.56/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.56/0.74  thf('5', plain,
% 0.56/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.56/0.74           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.56/0.74  thf('6', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X22 @ X23)
% 0.56/0.74           = (k5_xboole_0 @ X22 @ 
% 0.56/0.74              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 0.56/0.74      inference('demod', [status(thm)], ['4', '5'])).
% 0.56/0.74  thf('7', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.56/0.74           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['3', '6'])).
% 0.56/0.74  thf(t5_boole, axiom,
% 0.56/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.56/0.74  thf('8', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.56/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.74  thf('9', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['7', '8'])).
% 0.56/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.56/0.74  thf('10', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.56/0.74  thf('11', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.56/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.74  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.56/0.74  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['9', '12'])).
% 0.56/0.74  thf(t79_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.56/0.74  thf('14', plain,
% 0.56/0.74      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.56/0.74      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.56/0.74  thf(t87_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( r1_xboole_0 @ A @ B ) =>
% 0.56/0.74       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 0.56/0.74         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 0.56/0.74  thf('15', plain,
% 0.56/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.56/0.74         (~ (r1_xboole_0 @ X16 @ X17)
% 0.56/0.74          | ((k2_xboole_0 @ (k4_xboole_0 @ X18 @ X16) @ X17)
% 0.56/0.74              = (k4_xboole_0 @ (k2_xboole_0 @ X18 @ X17) @ X16)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t87_xboole_1])).
% 0.56/0.74  thf('16', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 0.56/0.74           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.74  thf('17', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ 
% 0.56/0.74           (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 0.56/0.74           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['13', '16'])).
% 0.56/0.74  thf('18', plain,
% 0.56/0.74      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t4_boole])).
% 0.56/0.74  thf('19', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.56/0.74           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['17', '18'])).
% 0.56/0.74  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['9', '12'])).
% 0.56/0.74  thf('21', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['19', '20'])).
% 0.56/0.74  thf(t41_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.56/0.74       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.56/0.74  thf('22', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.74           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.74  thf(t39_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.56/0.74  thf('23', plain,
% 0.56/0.74      (![X2 : $i, X3 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.56/0.74           = (k2_xboole_0 @ X2 @ X3))),
% 0.56/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.74  thf('24', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.56/0.74           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['22', '23'])).
% 0.56/0.74  thf('25', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.56/0.74           = (k3_xboole_0 @ X10 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.74  thf('26', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.74           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.74  thf('27', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.56/0.74           = (k4_xboole_0 @ X2 @ 
% 0.56/0.74              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.56/0.74      inference('sup+', [status(thm)], ['25', '26'])).
% 0.56/0.74  thf('28', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.74           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.74  thf('29', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.56/0.74           = (k4_xboole_0 @ X2 @ 
% 0.56/0.74              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.56/0.74      inference('demod', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf('30', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.56/0.74           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.56/0.74      inference('sup+', [status(thm)], ['24', '29'])).
% 0.56/0.74  thf('31', plain,
% 0.56/0.74      (![X2 : $i, X3 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.56/0.74           = (k2_xboole_0 @ X2 @ X3))),
% 0.56/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.74  thf('32', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.56/0.74           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.56/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.56/0.74  thf('33', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.74           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.74  thf(t3_boole, axiom,
% 0.56/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.56/0.74  thf('34', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.56/0.74  thf('35', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.56/0.74           = (k3_xboole_0 @ X10 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.74  thf('36', plain,
% 0.56/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['34', '35'])).
% 0.56/0.74  thf('37', plain,
% 0.56/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['34', '35'])).
% 0.56/0.74  thf('38', plain,
% 0.56/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.56/0.74           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.56/0.74  thf('39', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 0.56/0.74           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['37', '38'])).
% 0.56/0.74  thf(t46_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.56/0.74  thf('40', plain,
% 0.56/0.74      (![X8 : $i, X9 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.56/0.74  thf('41', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.56/0.74  thf('42', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.56/0.74  thf('43', plain,
% 0.56/0.74      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['41', '42'])).
% 0.56/0.74  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['36', '43'])).
% 0.56/0.74  thf('45', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.56/0.74           = (k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['33', '44'])).
% 0.56/0.74  thf('46', plain,
% 0.56/0.74      (![X2 : $i, X3 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.56/0.74           = (k2_xboole_0 @ X2 @ X3))),
% 0.56/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.74  thf('47', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['45', '46'])).
% 0.56/0.74  thf('48', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['32', '47'])).
% 0.56/0.74  thf('49', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['21', '48'])).
% 0.56/0.74  thf('50', plain,
% 0.56/0.74      (![X22 : $i, X23 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X22 @ X23)
% 0.56/0.74           = (k5_xboole_0 @ X22 @ 
% 0.56/0.74              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 0.56/0.74      inference('demod', [status(thm)], ['4', '5'])).
% 0.56/0.74  thf('51', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.56/0.74           = (k5_xboole_0 @ X0 @ 
% 0.56/0.74              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['49', '50'])).
% 0.56/0.74  thf('52', plain,
% 0.56/0.74      (![X2 : $i, X3 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.56/0.74           = (k2_xboole_0 @ X2 @ X3))),
% 0.56/0.74      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.56/0.74  thf('53', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.56/0.74  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.56/0.74  thf('55', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X0 @ X1)
% 0.56/0.74           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.56/0.74  thf('56', plain,
% 0.56/0.74      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.56/0.74      inference('demod', [status(thm)], ['0', '55'])).
% 0.56/0.74  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.56/0.74  
% 0.56/0.74  % SZS output end Refutation
% 0.56/0.74  
% 0.56/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
