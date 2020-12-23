%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w6gN1Hm31A

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:57 EST 2020

% Result     : Theorem 31.45s
% Output     : Refutation 31.45s
% Verified   : 
% Statistics : Number of formulae       :  309 (7449 expanded)
%              Number of leaves         :   17 (2507 expanded)
%              Depth                    :   35
%              Number of atoms          : 3086 (68868 expanded)
%              Number of equality atoms :  291 (7110 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','33'])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','79','80'])).

thf('82',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','83'])).

thf('85',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('101',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','83'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('121',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['119','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['108','109','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('133',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['130','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['129','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','79','80'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('143',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
       != ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('153',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
       != X1 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['148','156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
       != X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['141','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
       != X0 )
      | ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['140','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('162',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['160','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','169'])).

thf('171',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('172',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['170','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','139'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('179',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['177','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('185',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('188',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['183','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','139'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','201','202','205'])).

thf('207',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('208',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('211',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['209','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('223',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('227',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['222','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['221','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['218','219','220','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('233',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('234',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['232','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('246',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('248',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['231','248'])).

thf('250',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('254',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('259',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('266',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['262','263','266','267','268','269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['253','270'])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['252','271'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['253','270'])).

thf('274',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('275',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['272','273','274'])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['262','263','266','267','268','269'])).

thf('278',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['251','275','276','277'])).

thf('279',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['131','136'])).

thf('280',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('281',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('282',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('283',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('285',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X2
      = ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['283','284'])).

thf('286',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X2
      = ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['280','285'])).

thf('287',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['279','286'])).

thf('288',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','206','278','287'])).

thf('289',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','288'])).

thf('290',plain,(
    $false ),
    inference(simplify,[status(thm)],['289'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w6gN1Hm31A
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 31.45/31.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 31.45/31.70  % Solved by: fo/fo7.sh
% 31.45/31.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.45/31.70  % done 29078 iterations in 31.239s
% 31.45/31.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 31.45/31.70  % SZS output start Refutation
% 31.45/31.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 31.45/31.70  thf(sk_B_type, type, sk_B: $i).
% 31.45/31.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 31.45/31.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 31.45/31.70  thf(sk_A_type, type, sk_A: $i).
% 31.45/31.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 31.45/31.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 31.45/31.70  thf(t94_xboole_1, conjecture,
% 31.45/31.70    (![A:$i,B:$i]:
% 31.45/31.70     ( ( k2_xboole_0 @ A @ B ) =
% 31.45/31.70       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 31.45/31.70  thf(zf_stmt_0, negated_conjecture,
% 31.45/31.70    (~( ![A:$i,B:$i]:
% 31.45/31.70        ( ( k2_xboole_0 @ A @ B ) =
% 31.45/31.70          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 31.45/31.70    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 31.45/31.70  thf('0', plain,
% 31.45/31.70      (((k2_xboole_0 @ sk_A @ sk_B)
% 31.45/31.70         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 31.45/31.70             (k3_xboole_0 @ sk_A @ sk_B)))),
% 31.45/31.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.45/31.70  thf(d6_xboole_0, axiom,
% 31.45/31.70    (![A:$i,B:$i]:
% 31.45/31.70     ( ( k5_xboole_0 @ A @ B ) =
% 31.45/31.70       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 31.45/31.70  thf('1', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf(commutativity_k2_xboole_0, axiom,
% 31.45/31.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 31.45/31.70  thf('2', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('3', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k5_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['1', '2'])).
% 31.45/31.70  thf('4', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('5', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['3', '4'])).
% 31.45/31.70  thf('6', plain,
% 31.45/31.70      (((k2_xboole_0 @ sk_A @ sk_B)
% 31.45/31.70         != (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 31.45/31.70             (k5_xboole_0 @ sk_A @ sk_B)))),
% 31.45/31.70      inference('demod', [status(thm)], ['0', '5'])).
% 31.45/31.70  thf('7', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['3', '4'])).
% 31.45/31.70  thf('8', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf(t39_xboole_1, axiom,
% 31.45/31.70    (![A:$i,B:$i]:
% 31.45/31.70     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 31.45/31.70  thf('9', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('10', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf(t40_xboole_1, axiom,
% 31.45/31.70    (![A:$i,B:$i]:
% 31.45/31.70     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 31.45/31.70  thf('11', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('12', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('13', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['9', '12'])).
% 31.45/31.70  thf('14', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('15', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['13', '14'])).
% 31.45/31.70  thf(t41_xboole_1, axiom,
% 31.45/31.70    (![A:$i,B:$i,C:$i]:
% 31.45/31.70     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 31.45/31.70       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 31.45/31.70  thf('16', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('17', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['15', '16'])).
% 31.45/31.70  thf('18', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf(t83_xboole_1, axiom,
% 31.45/31.70    (![A:$i,B:$i]:
% 31.45/31.70     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 31.45/31.70  thf('19', plain,
% 31.45/31.70      (![X15 : $i, X17 : $i]:
% 31.45/31.70         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t83_xboole_1])).
% 31.45/31.70  thf('20', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70            != (k4_xboole_0 @ X2 @ X1))
% 31.45/31.70          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['18', '19'])).
% 31.45/31.70  thf('21', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['17', '20'])).
% 31.45/31.70  thf('22', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 31.45/31.70      inference('simplify', [status(thm)], ['21'])).
% 31.45/31.70  thf(symmetry_r1_xboole_0, axiom,
% 31.45/31.70    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 31.45/31.70  thf('23', plain,
% 31.45/31.70      (![X4 : $i, X5 : $i]:
% 31.45/31.70         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 31.45/31.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 31.45/31.70  thf('24', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['22', '23'])).
% 31.45/31.70  thf('25', plain,
% 31.45/31.70      (![X15 : $i, X16 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 31.45/31.70      inference('cnf', [status(esa)], [t83_xboole_1])).
% 31.45/31.70  thf('26', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['24', '25'])).
% 31.45/31.70  thf('27', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('28', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['26', '27'])).
% 31.45/31.70  thf('29', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['8', '28'])).
% 31.45/31.70  thf(t48_xboole_1, axiom,
% 31.45/31.70    (![A:$i,B:$i]:
% 31.45/31.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 31.45/31.70  thf('30', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('31', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['29', '30'])).
% 31.45/31.70  thf('32', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 31.45/31.70      inference('simplify', [status(thm)], ['21'])).
% 31.45/31.70  thf('33', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['31', '32'])).
% 31.45/31.70  thf('34', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['7', '33'])).
% 31.45/31.70  thf('35', plain,
% 31.45/31.70      (![X15 : $i, X16 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 31.45/31.70      inference('cnf', [status(esa)], [t83_xboole_1])).
% 31.45/31.70  thf('36', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['34', '35'])).
% 31.45/31.70  thf('37', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('38', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70              (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 31.45/31.70      inference('sup+', [status(thm)], ['36', '37'])).
% 31.45/31.70  thf(t93_xboole_1, axiom,
% 31.45/31.70    (![A:$i,B:$i]:
% 31.45/31.70     ( ( k2_xboole_0 @ A @ B ) =
% 31.45/31.70       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 31.45/31.70  thf('39', plain,
% 31.45/31.70      (![X18 : $i, X19 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X18 @ X19)
% 31.45/31.70           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 31.45/31.70              (k3_xboole_0 @ X18 @ X19)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t93_xboole_1])).
% 31.45/31.70  thf('40', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('41', plain,
% 31.45/31.70      (![X18 : $i, X19 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X18 @ X19)
% 31.45/31.70           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 31.45/31.70              (k5_xboole_0 @ X18 @ X19)))),
% 31.45/31.70      inference('demod', [status(thm)], ['39', '40'])).
% 31.45/31.70  thf('42', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('43', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('44', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 31.45/31.70      inference('sup+', [status(thm)], ['42', '43'])).
% 31.45/31.70  thf('45', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['3', '4'])).
% 31.45/31.70  thf('46', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 31.45/31.70      inference('demod', [status(thm)], ['44', '45'])).
% 31.45/31.70  thf('47', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))
% 31.45/31.70           = (k2_xboole_0 @ 
% 31.45/31.70              (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 31.45/31.70              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 31.45/31.70      inference('sup+', [status(thm)], ['41', '46'])).
% 31.45/31.70  thf('48', plain,
% 31.45/31.70      (![X18 : $i, X19 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X18 @ X19)
% 31.45/31.70           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 31.45/31.70              (k5_xboole_0 @ X18 @ X19)))),
% 31.45/31.70      inference('demod', [status(thm)], ['39', '40'])).
% 31.45/31.70  thf('49', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ 
% 31.45/31.70              (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 31.45/31.70              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 31.45/31.70      inference('demod', [status(thm)], ['47', '48'])).
% 31.45/31.70  thf('50', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('51', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('52', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('53', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('54', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('55', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['53', '54'])).
% 31.45/31.70  thf('56', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('57', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('58', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['56', '57'])).
% 31.45/31.70  thf('59', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['55', '58'])).
% 31.45/31.70  thf('60', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('61', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['15', '16'])).
% 31.45/31.70  thf('62', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['60', '61'])).
% 31.45/31.70  thf('63', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['59', '62'])).
% 31.45/31.70  thf('64', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['60', '61'])).
% 31.45/31.70  thf('65', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('66', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['64', '65'])).
% 31.45/31.70  thf('67', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0)
% 31.45/31.70           = (k3_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['63', '66'])).
% 31.45/31.70  thf('68', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['24', '25'])).
% 31.45/31.70  thf('69', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('70', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['68', '69'])).
% 31.45/31.70  thf('71', plain,
% 31.45/31.70      (![X0 : $i]: ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['67', '70'])).
% 31.45/31.70  thf('72', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['52', '71'])).
% 31.45/31.70  thf('73', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('74', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['15', '16'])).
% 31.45/31.70  thf('75', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('76', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['74', '75'])).
% 31.45/31.70  thf('77', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('78', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ X1 @ X0)
% 31.45/31.70           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['76', '77'])).
% 31.45/31.70  thf('79', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['73', '78'])).
% 31.45/31.70  thf('80', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['68', '69'])).
% 31.45/31.70  thf('81', plain,
% 31.45/31.70      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['72', '79', '80'])).
% 31.45/31.70  thf('82', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('83', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['81', '82'])).
% 31.45/31.70  thf('84', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['51', '83'])).
% 31.45/31.70  thf('85', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('86', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('87', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('88', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['86', '87'])).
% 31.45/31.70  thf('89', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('90', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 31.45/31.70      inference('demod', [status(thm)], ['88', '89'])).
% 31.45/31.70  thf('91', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['85', '90'])).
% 31.45/31.70  thf('92', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['60', '61'])).
% 31.45/31.70  thf('93', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['15', '16'])).
% 31.45/31.70  thf('94', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['91', '92', '93'])).
% 31.45/31.70  thf('95', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('96', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 31.45/31.70              (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))))),
% 31.45/31.70      inference('sup+', [status(thm)], ['94', '95'])).
% 31.45/31.70  thf('97', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['91', '92', '93'])).
% 31.45/31.70  thf('98', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k5_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['1', '2'])).
% 31.45/31.70  thf('99', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k5_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['96', '97', '98'])).
% 31.45/31.70  thf('100', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('101', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('102', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['100', '101'])).
% 31.45/31.70  thf('103', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('104', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('105', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['56', '57'])).
% 31.45/31.70  thf('106', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 31.45/31.70              (k2_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['104', '105'])).
% 31.45/31.70  thf('107', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('108', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['106', '107'])).
% 31.45/31.70  thf('109', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['51', '83'])).
% 31.45/31.70  thf('110', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('111', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('112', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['110', '111'])).
% 31.45/31.70  thf('113', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('114', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('115', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['112', '113', '114'])).
% 31.45/31.70  thf('116', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['53', '54'])).
% 31.45/31.70  thf('117', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 31.45/31.70              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))))),
% 31.45/31.70      inference('sup+', [status(thm)], ['115', '116'])).
% 31.45/31.70  thf('118', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('119', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 31.45/31.70              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))))),
% 31.45/31.70      inference('demod', [status(thm)], ['117', '118'])).
% 31.45/31.70  thf('120', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('121', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('122', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['120', '121'])).
% 31.45/31.70  thf('123', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('124', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 31.45/31.70      inference('demod', [status(thm)], ['122', '123'])).
% 31.45/31.70  thf('125', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['24', '25'])).
% 31.45/31.70  thf('126', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['119', '124', '125'])).
% 31.45/31.70  thf('127', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['108', '109', '126'])).
% 31.45/31.70  thf('128', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) @ 
% 31.45/31.70           (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['99', '127'])).
% 31.45/31.70  thf('129', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['56', '57'])).
% 31.45/31.70  thf('130', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('131', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['24', '25'])).
% 31.45/31.70  thf('132', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('133', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('134', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['132', '133'])).
% 31.45/31.70  thf('135', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['53', '54'])).
% 31.45/31.70  thf('136', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['134', '135'])).
% 31.45/31.70  thf('137', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['131', '136'])).
% 31.45/31.70  thf('138', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['130', '137'])).
% 31.45/31.70  thf('139', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['129', '138'])).
% 31.45/31.70  thf('140', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((X1) = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['128', '139'])).
% 31.45/31.70  thf('141', plain,
% 31.45/31.70      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['72', '79', '80'])).
% 31.45/31.70  thf('142', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['53', '54'])).
% 31.45/31.70  thf('143', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('144', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 31.45/31.70              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['142', '143'])).
% 31.45/31.70  thf('145', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('146', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 31.45/31.70              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 31.45/31.70      inference('demod', [status(thm)], ['144', '145'])).
% 31.45/31.70  thf('147', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70            != (k4_xboole_0 @ X2 @ X1))
% 31.45/31.70          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['18', '19'])).
% 31.45/31.70  thf('148', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 31.45/31.70            != (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X2 @ X1)))
% 31.45/31.70          | (r1_xboole_0 @ 
% 31.45/31.70             (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X2 @ X1)) @ 
% 31.45/31.70             X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['146', '147'])).
% 31.45/31.70  thf('149', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('150', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['53', '54'])).
% 31.45/31.70  thf('151', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['149', '150'])).
% 31.45/31.70  thf('152', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('153', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('154', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['151', '152', '153'])).
% 31.45/31.70  thf('155', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['24', '25'])).
% 31.45/31.70  thf('156', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['154', '155'])).
% 31.45/31.70  thf('157', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['154', '155'])).
% 31.45/31.70  thf('158', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 31.45/31.70            != (X1))
% 31.45/31.70          | (r1_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['148', '156', '157'])).
% 31.45/31.70  thf('159', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 31.45/31.70            != (X0))
% 31.45/31.70          | (r1_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup-', [status(thm)], ['141', '158'])).
% 31.45/31.70  thf('160', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) != (X0))
% 31.45/31.70          | (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('sup-', [status(thm)], ['140', '159'])).
% 31.45/31.70  thf('161', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['64', '65'])).
% 31.45/31.70  thf('162', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['68', '69'])).
% 31.45/31.70  thf('163', plain,
% 31.45/31.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['161', '162'])).
% 31.45/31.70  thf('164', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         (((X0) != (X0)) | (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['160', '163'])).
% 31.45/31.70  thf('165', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1))),
% 31.45/31.70      inference('simplify', [status(thm)], ['164'])).
% 31.45/31.70  thf('166', plain,
% 31.45/31.70      (![X4 : $i, X5 : $i]:
% 31.45/31.70         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 31.45/31.70      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 31.45/31.70  thf('167', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 31.45/31.70      inference('sup-', [status(thm)], ['165', '166'])).
% 31.45/31.70  thf('168', plain,
% 31.45/31.70      (![X15 : $i, X16 : $i]:
% 31.45/31.70         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 31.45/31.70      inference('cnf', [status(esa)], [t83_xboole_1])).
% 31.45/31.70  thf('169', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 31.45/31.70           = (k5_xboole_0 @ X1 @ X1))),
% 31.45/31.70      inference('sup-', [status(thm)], ['167', '168'])).
% 31.45/31.70  thf('170', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X0 @ X0)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['84', '169'])).
% 31.45/31.70  thf('171', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('172', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('173', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['171', '172'])).
% 31.45/31.70  thf('174', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['170', '173'])).
% 31.45/31.70  thf('175', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((X1) = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['128', '139'])).
% 31.45/31.70  thf('176', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['174', '175'])).
% 31.45/31.70  thf('177', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['50', '176'])).
% 31.45/31.70  thf('178', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('179', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('180', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['178', '179'])).
% 31.45/31.70  thf('181', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('182', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 31.45/31.70      inference('demod', [status(thm)], ['180', '181'])).
% 31.45/31.70  thf('183', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['177', '182'])).
% 31.45/31.70  thf('184', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k3_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['64', '65'])).
% 31.45/31.70  thf('185', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('186', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['184', '185'])).
% 31.45/31.70  thf('187', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('188', plain,
% 31.45/31.70      (![X18 : $i, X19 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X18 @ X19)
% 31.45/31.70           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 31.45/31.70              (k5_xboole_0 @ X18 @ X19)))),
% 31.45/31.70      inference('demod', [status(thm)], ['39', '40'])).
% 31.45/31.70  thf('189', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('190', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ X0)
% 31.45/31.70           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 31.45/31.70  thf('191', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('192', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0)
% 31.45/31.70           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['190', '191'])).
% 31.45/31.70  thf('193', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['10', '11'])).
% 31.45/31.70  thf('194', plain,
% 31.45/31.70      (![X0 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X0)
% 31.45/31.70           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['192', '193'])).
% 31.45/31.70  thf('195', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('196', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 31.45/31.70           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['194', '195'])).
% 31.45/31.70  thf('197', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('198', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['196', '197'])).
% 31.45/31.70  thf('199', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 31.45/31.70           = (k5_xboole_0 @ X1 @ X1))),
% 31.45/31.70      inference('sup-', [status(thm)], ['167', '168'])).
% 31.45/31.70  thf('200', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k5_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['198', '199'])).
% 31.45/31.70  thf('201', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k5_xboole_0 @ X0 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['183', '200'])).
% 31.45/31.70  thf('202', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('203', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((X1) = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['128', '139'])).
% 31.45/31.70  thf('204', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('205', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['203', '204'])).
% 31.45/31.70  thf('206', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['49', '201', '202', '205'])).
% 31.45/31.70  thf('207', plain,
% 31.45/31.70      (![X18 : $i, X19 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X18 @ X19)
% 31.45/31.70           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 31.45/31.70              (k5_xboole_0 @ X18 @ X19)))),
% 31.45/31.70      inference('demod', [status(thm)], ['39', '40'])).
% 31.45/31.70  thf('208', plain,
% 31.45/31.70      (![X8 : $i, X9 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 31.45/31.70           = (k4_xboole_0 @ X8 @ X9))),
% 31.45/31.70      inference('cnf', [status(esa)], [t40_xboole_1])).
% 31.45/31.70  thf('209', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['207', '208'])).
% 31.45/31.70  thf('210', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 31.45/31.70      inference('sup-', [status(thm)], ['24', '25'])).
% 31.45/31.70  thf('211', plain,
% 31.45/31.70      (![X2 : $i, X3 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X2 @ X3)
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 31.45/31.70      inference('cnf', [status(esa)], [d6_xboole_0])).
% 31.45/31.70  thf('212', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['210', '211'])).
% 31.45/31.70  thf('213', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('214', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['15', '16'])).
% 31.45/31.70  thf('215', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['212', '213', '214'])).
% 31.45/31.70  thf('216', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('217', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['215', '216'])).
% 31.45/31.70  thf('218', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))
% 31.45/31.70           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['209', '217'])).
% 31.45/31.70  thf('219', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['215', '216'])).
% 31.45/31.70  thf('220', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('221', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['3', '4'])).
% 31.45/31.70  thf('222', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('223', plain,
% 31.45/31.70      (![X18 : $i, X19 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X18 @ X19)
% 31.45/31.70           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 31.45/31.70              (k5_xboole_0 @ X18 @ X19)))),
% 31.45/31.70      inference('demod', [status(thm)], ['39', '40'])).
% 31.45/31.70  thf('224', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('225', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['223', '224'])).
% 31.45/31.70  thf('226', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('227', plain,
% 31.45/31.70      (![X18 : $i, X19 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X18 @ X19)
% 31.45/31.70           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 31.45/31.70              (k5_xboole_0 @ X18 @ X19)))),
% 31.45/31.70      inference('demod', [status(thm)], ['39', '40'])).
% 31.45/31.70  thf('228', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['225', '226', '227'])).
% 31.45/31.70  thf('229', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['222', '228'])).
% 31.45/31.70  thf('230', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['221', '229'])).
% 31.45/31.70  thf('231', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['218', '219', '220', '230'])).
% 31.45/31.70  thf('232', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ X1 @ X0)
% 31.45/31.70           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['76', '77'])).
% 31.45/31.70  thf('233', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('234', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('235', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['233', '234'])).
% 31.45/31.70  thf('236', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('237', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('238', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['235', '236', '237'])).
% 31.45/31.70  thf('239', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0))))),
% 31.45/31.70      inference('sup+', [status(thm)], ['232', '238'])).
% 31.45/31.70  thf('240', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['15', '16'])).
% 31.45/31.70  thf('241', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['15', '16'])).
% 31.45/31.70  thf('242', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('demod', [status(thm)], ['239', '240', '241'])).
% 31.45/31.70  thf('243', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['174', '175'])).
% 31.45/31.70  thf('244', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['242', '243'])).
% 31.45/31.70  thf('245', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 31.45/31.70      inference('demod', [status(thm)], ['180', '181'])).
% 31.45/31.70  thf('246', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X2 @ 
% 31.45/31.70           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['244', '245'])).
% 31.45/31.70  thf('247', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (X1))),
% 31.45/31.70      inference('demod', [status(thm)], ['242', '243'])).
% 31.45/31.70  thf('248', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X2 @ X0)
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['246', '247'])).
% 31.45/31.70  thf('249', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0)
% 31.45/31.70           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['231', '248'])).
% 31.45/31.70  thf('250', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('251', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['249', '250'])).
% 31.45/31.70  thf('252', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('253', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('254', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('255', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('256', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['254', '255'])).
% 31.45/31.70  thf('257', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('258', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('259', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('260', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 31.45/31.70  thf('261', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 31.45/31.70  thf('262', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.45/31.70           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))
% 31.45/31.70           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['260', '261'])).
% 31.45/31.70  thf('263', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('264', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('265', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['102', '103'])).
% 31.45/31.70  thf('266', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['264', '265'])).
% 31.45/31.70  thf('267', plain,
% 31.45/31.70      (![X6 : $i, X7 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 31.45/31.70           = (k2_xboole_0 @ X6 @ X7))),
% 31.45/31.70      inference('cnf', [status(esa)], [t39_xboole_1])).
% 31.45/31.70  thf('268', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('269', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 31.45/31.70  thf('270', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)],
% 31.45/31.70                ['262', '263', '266', '267', '268', '269'])).
% 31.45/31.70  thf('271', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['253', '270'])).
% 31.45/31.70  thf('272', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['252', '271'])).
% 31.45/31.70  thf('273', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('sup+', [status(thm)], ['253', '270'])).
% 31.45/31.70  thf('274', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('275', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ X1)
% 31.45/31.70           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['272', '273', '274'])).
% 31.45/31.70  thf('276', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.45/31.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 31.45/31.70  thf('277', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)],
% 31.45/31.70                ['262', '263', '266', '267', '268', '269'])).
% 31.45/31.70  thf('278', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['251', '275', '276', '277'])).
% 31.45/31.70  thf('279', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 31.45/31.70      inference('sup+', [status(thm)], ['131', '136'])).
% 31.45/31.70  thf('280', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('281', plain,
% 31.45/31.70      (![X13 : $i, X14 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 31.45/31.70           = (k3_xboole_0 @ X13 @ X14))),
% 31.45/31.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 31.45/31.70  thf('282', plain,
% 31.45/31.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 31.45/31.70           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 31.45/31.70      inference('cnf', [status(esa)], [t41_xboole_1])).
% 31.45/31.70  thf('283', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 31.45/31.70           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['281', '282'])).
% 31.45/31.70  thf('284', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('demod', [status(thm)], ['174', '175'])).
% 31.45/31.70  thf('285', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((X2)
% 31.45/31.70           = (k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['283', '284'])).
% 31.45/31.70  thf('286', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((X2)
% 31.45/31.70           = (k2_xboole_0 @ X2 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['280', '285'])).
% 31.45/31.70  thf('287', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.45/31.70         ((k2_xboole_0 @ X0 @ X2)
% 31.45/31.70           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X0 @ X1)))),
% 31.45/31.70      inference('sup+', [status(thm)], ['279', '286'])).
% 31.45/31.70  thf('288', plain,
% 31.45/31.70      (![X0 : $i, X1 : $i]:
% 31.45/31.70         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 31.45/31.70           = (k2_xboole_0 @ X1 @ X0))),
% 31.45/31.70      inference('demod', [status(thm)], ['38', '206', '278', '287'])).
% 31.45/31.70  thf('289', plain,
% 31.45/31.70      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 31.45/31.70      inference('demod', [status(thm)], ['6', '288'])).
% 31.45/31.70  thf('290', plain, ($false), inference('simplify', [status(thm)], ['289'])).
% 31.45/31.70  
% 31.45/31.70  % SZS output end Refutation
% 31.45/31.70  
% 31.45/31.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
