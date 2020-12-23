%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pApXjD72av

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:36 EST 2020

% Result     : Theorem 2.64s
% Output     : Refutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 152 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :   25
%              Number of atoms          :  876 (1244 expanded)
%              Number of equality atoms :   71 ( 106 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18','27','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ) ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ) ) ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['7','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('52',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','77'])).

thf('79',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('80',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('85',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['0','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pApXjD72av
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.64/2.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.64/2.84  % Solved by: fo/fo7.sh
% 2.64/2.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.64/2.84  % done 3654 iterations in 2.387s
% 2.64/2.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.64/2.84  % SZS output start Refutation
% 2.64/2.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.64/2.84  thf(sk_C_type, type, sk_C: $i).
% 2.64/2.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.64/2.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.64/2.84  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.64/2.84  thf(sk_A_type, type, sk_A: $i).
% 2.64/2.84  thf(sk_B_type, type, sk_B: $i).
% 2.64/2.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.64/2.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.64/2.84  thf(t81_xboole_1, conjecture,
% 2.64/2.84    (![A:$i,B:$i,C:$i]:
% 2.64/2.84     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.64/2.84       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 2.64/2.84  thf(zf_stmt_0, negated_conjecture,
% 2.64/2.84    (~( ![A:$i,B:$i,C:$i]:
% 2.64/2.84        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.64/2.84          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 2.64/2.84    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 2.64/2.84  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf(t39_xboole_1, axiom,
% 2.64/2.84    (![A:$i,B:$i]:
% 2.64/2.84     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.64/2.84  thf('1', plain,
% 2.64/2.84      (![X12 : $i, X13 : $i]:
% 2.64/2.84         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.64/2.84           = (k2_xboole_0 @ X12 @ X13))),
% 2.64/2.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.64/2.84  thf(t48_xboole_1, axiom,
% 2.64/2.84    (![A:$i,B:$i]:
% 2.64/2.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.64/2.84  thf('2', plain,
% 2.64/2.84      (![X18 : $i, X19 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.64/2.84           = (k3_xboole_0 @ X18 @ X19))),
% 2.64/2.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.64/2.84  thf(t41_xboole_1, axiom,
% 2.64/2.84    (![A:$i,B:$i,C:$i]:
% 2.64/2.84     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.64/2.84       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.64/2.84  thf('3', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('4', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.84         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 2.64/2.84           = (k4_xboole_0 @ X2 @ 
% 2.64/2.84              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 2.64/2.84      inference('sup+', [status(thm)], ['2', '3'])).
% 2.64/2.84  thf('5', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('6', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.84         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 2.64/2.84           = (k4_xboole_0 @ X2 @ 
% 2.64/2.84              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 2.64/2.84      inference('demod', [status(thm)], ['4', '5'])).
% 2.64/2.84  thf('7', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.84         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 2.64/2.84           = (k4_xboole_0 @ X2 @ 
% 2.64/2.84              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 2.64/2.84      inference('sup+', [status(thm)], ['1', '6'])).
% 2.64/2.84  thf('8', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('9', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 2.64/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.64/2.84  thf(symmetry_r1_xboole_0, axiom,
% 2.64/2.84    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.64/2.84  thf('10', plain,
% 2.64/2.84      (![X4 : $i, X5 : $i]:
% 2.64/2.84         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 2.64/2.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.64/2.84  thf('11', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 2.64/2.84      inference('sup-', [status(thm)], ['9', '10'])).
% 2.64/2.84  thf(d7_xboole_0, axiom,
% 2.64/2.84    (![A:$i,B:$i]:
% 2.64/2.84     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.64/2.84       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.64/2.84  thf('12', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.64/2.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.64/2.84  thf('13', plain,
% 2.64/2.84      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['11', '12'])).
% 2.64/2.84  thf('14', plain,
% 2.64/2.84      (![X18 : $i, X19 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.64/2.84           = (k3_xboole_0 @ X18 @ X19))),
% 2.64/2.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.64/2.84  thf('15', plain,
% 2.64/2.84      (![X12 : $i, X13 : $i]:
% 2.64/2.84         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.64/2.84           = (k2_xboole_0 @ X12 @ X13))),
% 2.64/2.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.64/2.84  thf('16', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.64/2.84           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.64/2.84      inference('sup+', [status(thm)], ['14', '15'])).
% 2.64/2.84  thf('17', plain,
% 2.64/2.84      (((k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A) @ 
% 2.64/2.84         k1_xboole_0)
% 2.64/2.84         = (k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A) @ 
% 2.64/2.84            (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.64/2.84      inference('sup+', [status(thm)], ['13', '16'])).
% 2.64/2.84  thf('18', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf(t3_boole, axiom,
% 2.64/2.84    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.64/2.84  thf('19', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 2.64/2.84      inference('cnf', [status(esa)], [t3_boole])).
% 2.64/2.84  thf(t36_xboole_1, axiom,
% 2.64/2.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.64/2.84  thf('20', plain,
% 2.64/2.84      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 2.64/2.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.64/2.84  thf('21', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.64/2.84      inference('sup+', [status(thm)], ['19', '20'])).
% 2.64/2.84  thf(l32_xboole_1, axiom,
% 2.64/2.84    (![A:$i,B:$i]:
% 2.64/2.84     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.64/2.84  thf('22', plain,
% 2.64/2.84      (![X6 : $i, X8 : $i]:
% 2.64/2.84         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 2.64/2.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.64/2.84  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['21', '22'])).
% 2.64/2.84  thf('24', plain,
% 2.64/2.84      (![X12 : $i, X13 : $i]:
% 2.64/2.84         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.64/2.84           = (k2_xboole_0 @ X12 @ X13))),
% 2.64/2.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.64/2.84  thf('25', plain,
% 2.64/2.84      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 2.64/2.84      inference('sup+', [status(thm)], ['23', '24'])).
% 2.64/2.84  thf(idempotence_k2_xboole_0, axiom,
% 2.64/2.84    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.64/2.84  thf('26', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 2.64/2.84      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.64/2.84  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.64/2.84      inference('demod', [status(thm)], ['25', '26'])).
% 2.64/2.84  thf('28', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('29', plain,
% 2.64/2.84      (((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A))
% 2.64/2.84         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A)) @ 
% 2.64/2.84            (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.64/2.84      inference('demod', [status(thm)], ['17', '18', '27', '28'])).
% 2.64/2.84  thf('30', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf(t79_xboole_1, axiom,
% 2.64/2.84    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.64/2.84  thf('31', plain,
% 2.64/2.84      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 2.64/2.84      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.64/2.84  thf('32', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.84         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 2.64/2.84      inference('sup+', [status(thm)], ['30', '31'])).
% 2.64/2.84  thf('33', plain,
% 2.64/2.84      (![X0 : $i]:
% 2.64/2.84         (r1_xboole_0 @ 
% 2.64/2.84          (k4_xboole_0 @ X0 @ 
% 2.64/2.84           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A))) @ 
% 2.64/2.84          (k4_xboole_0 @ sk_B @ sk_C))),
% 2.64/2.84      inference('sup+', [status(thm)], ['29', '32'])).
% 2.64/2.84  thf('34', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         (r1_xboole_0 @ 
% 2.64/2.84          (k4_xboole_0 @ X1 @ 
% 2.64/2.84           (k2_xboole_0 @ X0 @ 
% 2.64/2.84            (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A)))) @ 
% 2.64/2.84          (k4_xboole_0 @ sk_B @ sk_C))),
% 2.64/2.84      inference('sup+', [status(thm)], ['8', '33'])).
% 2.64/2.84  thf('35', plain,
% 2.64/2.84      ((r1_xboole_0 @ 
% 2.64/2.84        (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 2.64/2.84         (k4_xboole_0 @ sk_A @ sk_C)) @ 
% 2.64/2.84        (k4_xboole_0 @ sk_B @ sk_C))),
% 2.64/2.84      inference('sup+', [status(thm)], ['7', '34'])).
% 2.64/2.84  thf('36', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.64/2.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.64/2.84  thf('37', plain,
% 2.64/2.84      (((k3_xboole_0 @ 
% 2.64/2.84         (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 2.64/2.84          (k4_xboole_0 @ sk_A @ sk_C)) @ 
% 2.64/2.84         (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['35', '36'])).
% 2.64/2.84  thf('38', plain,
% 2.64/2.84      (![X18 : $i, X19 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.64/2.84           = (k3_xboole_0 @ X18 @ X19))),
% 2.64/2.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.64/2.84  thf('39', plain,
% 2.64/2.84      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 2.64/2.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.64/2.84  thf('40', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.64/2.84      inference('sup+', [status(thm)], ['38', '39'])).
% 2.64/2.84  thf('41', plain,
% 2.64/2.84      (![X6 : $i, X8 : $i]:
% 2.64/2.84         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 2.64/2.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.64/2.84  thf('42', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['40', '41'])).
% 2.64/2.84  thf('43', plain,
% 2.64/2.84      (![X18 : $i, X19 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.64/2.84           = (k3_xboole_0 @ X18 @ X19))),
% 2.64/2.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.64/2.84  thf('44', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 2.64/2.84           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 2.64/2.84      inference('sup+', [status(thm)], ['42', '43'])).
% 2.64/2.84  thf('45', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 2.64/2.84      inference('cnf', [status(esa)], [t3_boole])).
% 2.64/2.84  thf('46', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         ((k3_xboole_0 @ X0 @ X1)
% 2.64/2.84           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 2.64/2.84      inference('demod', [status(thm)], ['44', '45'])).
% 2.64/2.84  thf('47', plain,
% 2.64/2.84      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 2.64/2.84         (k4_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 2.64/2.84      inference('demod', [status(thm)], ['37', '46'])).
% 2.64/2.84  thf('48', plain,
% 2.64/2.84      (![X0 : $i, X2 : $i]:
% 2.64/2.84         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 2.64/2.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.64/2.84  thf('49', plain,
% 2.64/2.84      ((((k1_xboole_0) != (k1_xboole_0))
% 2.64/2.84        | (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ 
% 2.64/2.84           (k4_xboole_0 @ sk_A @ sk_C)))),
% 2.64/2.84      inference('sup-', [status(thm)], ['47', '48'])).
% 2.64/2.84  thf('50', plain,
% 2.64/2.84      ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_C))),
% 2.64/2.84      inference('simplify', [status(thm)], ['49'])).
% 2.64/2.84  thf('51', plain,
% 2.64/2.84      (![X4 : $i, X5 : $i]:
% 2.64/2.84         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 2.64/2.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.64/2.84  thf('52', plain,
% 2.64/2.84      ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 2.64/2.84      inference('sup-', [status(thm)], ['50', '51'])).
% 2.64/2.84  thf('53', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i]:
% 2.64/2.84         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.64/2.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.64/2.84  thf('54', plain,
% 2.64/2.84      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 2.64/2.84         (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['52', '53'])).
% 2.64/2.84  thf('55', plain,
% 2.64/2.84      (![X18 : $i, X19 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.64/2.84           = (k3_xboole_0 @ X18 @ X19))),
% 2.64/2.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.64/2.84  thf('56', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('57', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.64/2.84           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 2.64/2.84      inference('sup+', [status(thm)], ['55', '56'])).
% 2.64/2.84  thf('58', plain,
% 2.64/2.84      (![X6 : $i, X7 : $i]:
% 2.64/2.84         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 2.64/2.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.64/2.84  thf('59', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.84         (((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 2.64/2.84          | (r1_tarski @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 2.64/2.84      inference('sup-', [status(thm)], ['57', '58'])).
% 2.64/2.84  thf('60', plain,
% 2.64/2.84      (![X0 : $i]:
% 2.64/2.84         (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 2.64/2.84          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 2.64/2.84             (k2_xboole_0 @ 
% 2.64/2.84              (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 2.64/2.84               (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 2.64/2.84              X0)))),
% 2.64/2.84      inference('sup-', [status(thm)], ['54', '59'])).
% 2.64/2.84  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['21', '22'])).
% 2.64/2.84  thf('62', plain,
% 2.64/2.84      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 2.64/2.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.64/2.84  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.64/2.84      inference('sup+', [status(thm)], ['61', '62'])).
% 2.64/2.84  thf('64', plain,
% 2.64/2.84      (![X6 : $i, X8 : $i]:
% 2.64/2.84         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 2.64/2.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.64/2.84  thf('65', plain,
% 2.64/2.84      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['63', '64'])).
% 2.64/2.84  thf('66', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('67', plain,
% 2.64/2.84      (![X12 : $i, X13 : $i]:
% 2.64/2.84         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 2.64/2.84           = (k2_xboole_0 @ X12 @ X13))),
% 2.64/2.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.64/2.84  thf('68', plain,
% 2.64/2.84      (![X0 : $i]:
% 2.64/2.84         (((k1_xboole_0) != (k1_xboole_0))
% 2.64/2.84          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 2.64/2.84             (k2_xboole_0 @ 
% 2.64/2.84              (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ X0)))),
% 2.64/2.84      inference('demod', [status(thm)], ['60', '65', '66', '67'])).
% 2.64/2.84  thf('69', plain,
% 2.64/2.84      (![X0 : $i]:
% 2.64/2.84         (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 2.64/2.84          (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 2.64/2.84           X0))),
% 2.64/2.84      inference('simplify', [status(thm)], ['68'])).
% 2.64/2.84  thf('70', plain,
% 2.64/2.84      (![X6 : $i, X8 : $i]:
% 2.64/2.84         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 2.64/2.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.64/2.84  thf('71', plain,
% 2.64/2.84      (![X0 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 2.64/2.84           (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 2.64/2.84            X0))
% 2.64/2.84           = (k1_xboole_0))),
% 2.64/2.84      inference('sup-', [status(thm)], ['69', '70'])).
% 2.64/2.84  thf('72', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('73', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('74', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.64/2.84           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 2.64/2.84      inference('sup+', [status(thm)], ['55', '56'])).
% 2.64/2.84  thf('75', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 2.64/2.84           = (k4_xboole_0 @ X3 @ 
% 2.64/2.84              (k2_xboole_0 @ X2 @ 
% 2.64/2.84               (k2_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0))))),
% 2.64/2.84      inference('sup+', [status(thm)], ['73', '74'])).
% 2.64/2.84  thf('76', plain,
% 2.64/2.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 2.64/2.84           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 2.64/2.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.64/2.84  thf('77', plain,
% 2.64/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 2.64/2.84           = (k4_xboole_0 @ X3 @ 
% 2.64/2.84              (k2_xboole_0 @ X2 @ 
% 2.64/2.84               (k2_xboole_0 @ (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X1)) @ X0))))),
% 2.64/2.84      inference('demod', [status(thm)], ['75', '76'])).
% 2.64/2.84  thf('78', plain,
% 2.64/2.84      (![X0 : $i]:
% 2.64/2.84         ((k4_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) @ 
% 2.64/2.84           X0) = (k1_xboole_0))),
% 2.64/2.84      inference('demod', [status(thm)], ['71', '72', '77'])).
% 2.64/2.84  thf('79', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 2.64/2.84      inference('cnf', [status(esa)], [t3_boole])).
% 2.64/2.84  thf('80', plain,
% 2.64/2.84      (((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 2.64/2.84      inference('sup+', [status(thm)], ['78', '79'])).
% 2.64/2.84  thf('81', plain,
% 2.64/2.84      (![X0 : $i, X2 : $i]:
% 2.64/2.84         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 2.64/2.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.64/2.84  thf('82', plain,
% 2.64/2.84      ((((k1_xboole_0) != (k1_xboole_0))
% 2.64/2.84        | (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 2.64/2.84      inference('sup-', [status(thm)], ['80', '81'])).
% 2.64/2.84  thf('83', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 2.64/2.84      inference('simplify', [status(thm)], ['82'])).
% 2.64/2.84  thf('84', plain,
% 2.64/2.84      (![X4 : $i, X5 : $i]:
% 2.64/2.84         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 2.64/2.84      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.64/2.84  thf('85', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 2.64/2.84      inference('sup-', [status(thm)], ['83', '84'])).
% 2.64/2.84  thf('86', plain, ($false), inference('demod', [status(thm)], ['0', '85'])).
% 2.64/2.84  
% 2.64/2.84  % SZS output end Refutation
% 2.64/2.84  
% 2.64/2.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
