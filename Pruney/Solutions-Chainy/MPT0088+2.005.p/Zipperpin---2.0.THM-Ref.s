%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLT2NiExP5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:35 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 117 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  621 ( 896 expanded)
%              Number of equality atoms :   66 (  98 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','22'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['5','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','55','56'])).

thf('58',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LLT2NiExP5
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.79/0.98  % Solved by: fo/fo7.sh
% 0.79/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.98  % done 1141 iterations in 0.527s
% 0.79/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.79/0.98  % SZS output start Refutation
% 0.79/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.79/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.79/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.79/0.98  thf(t81_xboole_1, conjecture,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.79/0.98       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.79/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.79/0.98        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.79/0.98          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.79/0.98    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.79/0.98  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf(t48_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.79/0.98  thf('1', plain,
% 0.79/0.98      (![X16 : $i, X17 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.98           = (k3_xboole_0 @ X16 @ X17))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf(t41_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.79/0.98       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.79/0.98  thf('2', plain,
% 0.79/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.79/0.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.79/0.98  thf('3', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.79/0.98           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.79/0.98      inference('sup+', [status(thm)], ['1', '2'])).
% 0.79/0.98  thf(t49_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i,C:$i]:
% 0.79/0.98     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.79/0.98       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.79/0.98  thf('4', plain,
% 0.79/0.98      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.98           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.98      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.98  thf('5', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 0.79/0.98           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.79/0.98      inference('demod', [status(thm)], ['3', '4'])).
% 0.79/0.98  thf(commutativity_k2_xboole_0, axiom,
% 0.79/0.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.79/0.98  thf('6', plain,
% 0.79/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.79/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.79/0.98  thf('7', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.79/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.98  thf(d7_xboole_0, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.79/0.98       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.79/0.98  thf('8', plain,
% 0.79/0.98      (![X2 : $i, X3 : $i]:
% 0.79/0.98         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.79/0.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.79/0.98  thf('9', plain,
% 0.79/0.98      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.79/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.79/0.98  thf('10', plain,
% 0.79/0.98      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.98           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.98      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.98  thf('11', plain,
% 0.79/0.98      (![X0 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ sk_A @ 
% 0.79/0.98           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 0.79/0.98           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['9', '10'])).
% 0.79/0.98  thf('12', plain,
% 0.79/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.79/0.98           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.79/0.98  thf('13', plain,
% 0.79/0.98      (![X0 : $i]:
% 0.79/0.98         ((k3_xboole_0 @ sk_A @ 
% 0.79/0.98           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))
% 0.79/0.98           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.79/0.98      inference('demod', [status(thm)], ['11', '12'])).
% 0.79/0.98  thf(t36_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.79/0.98  thf('14', plain,
% 0.79/0.98      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.79/0.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.79/0.98  thf(t3_boole, axiom,
% 0.79/0.98    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.79/0.98  thf('15', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.79/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.98  thf('16', plain,
% 0.79/0.98      (![X16 : $i, X17 : $i]:
% 0.79/0.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.98           = (k3_xboole_0 @ X16 @ X17))),
% 0.79/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.98  thf('17', plain,
% 0.79/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.79/0.98      inference('sup+', [status(thm)], ['15', '16'])).
% 0.79/0.98  thf(t2_boole, axiom,
% 0.79/0.98    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.79/0.98  thf('18', plain,
% 0.79/0.98      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/0.98      inference('cnf', [status(esa)], [t2_boole])).
% 0.79/0.98  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/0.98      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/0.98  thf(t38_xboole_1, axiom,
% 0.79/0.98    (![A:$i,B:$i]:
% 0.79/0.98     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.79/0.98       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.79/0.98  thf('20', plain,
% 0.79/0.98      (![X8 : $i, X9 : $i]:
% 0.79/0.98         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.79/0.98      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.79/0.98  thf('21', plain,
% 0.79/0.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.79/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.79/0.99  thf('22', plain,
% 0.79/0.99      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.79/0.99      inference('sup-', [status(thm)], ['14', '21'])).
% 0.79/0.99  thf('23', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ sk_A @ 
% 0.79/0.99           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))) = (k1_xboole_0))),
% 0.79/0.99      inference('demod', [status(thm)], ['13', '22'])).
% 0.79/0.99  thf(t51_xboole_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.79/0.99       ( A ) ))).
% 0.79/0.99  thf('24', plain,
% 0.79/0.99      (![X21 : $i, X22 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.79/0.99           = (X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.79/0.99  thf('25', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.79/0.99           (k4_xboole_0 @ sk_A @ 
% 0.79/0.99            (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))))
% 0.79/0.99           = (sk_A))),
% 0.79/0.99      inference('sup+', [status(thm)], ['23', '24'])).
% 0.79/0.99  thf('26', plain,
% 0.79/0.99      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.79/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.79/0.99  thf('27', plain,
% 0.79/0.99      (![X21 : $i, X22 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.79/0.99           = (X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.79/0.99  thf('28', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['26', '27'])).
% 0.79/0.99  thf('29', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.79/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.99  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['28', '29'])).
% 0.79/0.99  thf('31', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ sk_A @ 
% 0.79/0.99           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))) = (sk_A))),
% 0.79/0.99      inference('demod', [status(thm)], ['25', '30'])).
% 0.79/0.99  thf('32', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ sk_A @ 
% 0.79/0.99           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C))) = (sk_A))),
% 0.79/0.99      inference('sup+', [status(thm)], ['6', '31'])).
% 0.79/0.99  thf('33', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ sk_A @ 
% 0.79/0.99           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))) = (sk_A))),
% 0.79/0.99      inference('sup+', [status(thm)], ['5', '32'])).
% 0.79/0.99  thf('34', plain,
% 0.79/0.99      (![X16 : $i, X17 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.99           = (k3_xboole_0 @ X16 @ X17))),
% 0.79/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.99  thf('35', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.99           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.99      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.99  thf('36', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X2 @ 
% 0.79/0.99           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 0.79/0.99           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/0.99  thf('37', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.99           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.99      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.99  thf('38', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X2 @ 
% 0.79/0.99           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 0.79/0.99           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['36', '37'])).
% 0.79/0.99  thf('39', plain,
% 0.79/0.99      (((k3_xboole_0 @ sk_B @ sk_A)
% 0.79/0.99         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['33', '38'])).
% 0.79/0.99  thf('40', plain,
% 0.79/0.99      (![X16 : $i, X17 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.99           = (k3_xboole_0 @ X16 @ X17))),
% 0.79/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.99  thf('41', plain,
% 0.79/0.99      (![X16 : $i, X17 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.99           = (k3_xboole_0 @ X16 @ X17))),
% 0.79/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.99  thf('42', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.79/0.99           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['40', '41'])).
% 0.79/0.99  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/0.99      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/0.99  thf('44', plain,
% 0.79/0.99      (![X16 : $i, X17 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.79/0.99           = (k3_xboole_0 @ X16 @ X17))),
% 0.79/0.99      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.79/0.99  thf('45', plain,
% 0.79/0.99      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['43', '44'])).
% 0.79/0.99  thf('46', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.79/0.99      inference('cnf', [status(esa)], [t3_boole])).
% 0.79/0.99  thf('47', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['45', '46'])).
% 0.79/0.99  thf('48', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.99           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.99      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.99  thf('49', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.79/0.99           = (k4_xboole_0 @ X0 @ X1))),
% 0.79/0.99      inference('sup+', [status(thm)], ['47', '48'])).
% 0.79/0.99  thf('50', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.79/0.99           = (k4_xboole_0 @ X1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['42', '49'])).
% 0.79/0.99  thf('51', plain,
% 0.79/0.99      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.79/0.99         (k3_xboole_0 @ sk_B @ sk_A))
% 0.79/0.99         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['39', '50'])).
% 0.79/0.99  thf('52', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.99           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.99      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.99  thf('53', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.99           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.99      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.99  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.79/0.99      inference('demod', [status(thm)], ['17', '18'])).
% 0.79/0.99  thf('55', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.79/0.99           = (k1_xboole_0))),
% 0.79/0.99      inference('sup+', [status(thm)], ['53', '54'])).
% 0.79/0.99  thf('56', plain,
% 0.79/0.99      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.79/0.99         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.79/0.99           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.79/0.99      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.79/0.99  thf('57', plain,
% 0.79/0.99      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.79/0.99      inference('demod', [status(thm)], ['51', '52', '55', '56'])).
% 0.79/0.99  thf('58', plain,
% 0.79/0.99      (![X2 : $i, X4 : $i]:
% 0.79/0.99         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.79/0.99      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.79/0.99  thf('59', plain,
% 0.79/0.99      ((((k1_xboole_0) != (k1_xboole_0))
% 0.79/0.99        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['57', '58'])).
% 0.79/0.99  thf('60', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.79/0.99      inference('simplify', [status(thm)], ['59'])).
% 0.79/0.99  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.79/0.99  
% 0.79/0.99  % SZS output end Refutation
% 0.79/0.99  
% 0.79/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
