%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.87uTfuJ9N0

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:35 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 114 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  626 ( 911 expanded)
%              Number of equality atoms :   65 (  97 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','37','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['21','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['44','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.87uTfuJ9N0
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:58:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.67  % Solved by: fo/fo7.sh
% 0.49/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.67  % done 500 iterations in 0.211s
% 0.49/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.67  % SZS output start Refutation
% 0.49/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.67  thf(t81_xboole_1, conjecture,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.49/0.67       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.49/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.67        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.49/0.67          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.49/0.67    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.49/0.67  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(t48_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('1', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.49/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf(d7_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.49/0.67       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.67  thf('3', plain,
% 0.49/0.67      (![X2 : $i, X3 : $i]:
% 0.49/0.67         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.49/0.67      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.49/0.67  thf('4', plain,
% 0.49/0.67      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.67  thf(t50_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.49/0.67       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.49/0.67  thf('5', plain,
% 0.49/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.49/0.67           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 0.49/0.67              (k3_xboole_0 @ X18 @ X20)))),
% 0.49/0.67      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.49/0.67  thf(t49_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.49/0.67       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.49/0.67  thf('6', plain,
% 0.49/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.49/0.67  thf('7', plain,
% 0.49/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.49/0.67           = (k3_xboole_0 @ X18 @ 
% 0.49/0.67              (k4_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X20))))),
% 0.49/0.67      inference('demod', [status(thm)], ['5', '6'])).
% 0.49/0.67  thf('8', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ sk_A @ 
% 0.49/0.67           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.49/0.67           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['4', '7'])).
% 0.49/0.67  thf(t3_boole, axiom,
% 0.49/0.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.67  thf('9', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.67  thf('10', plain,
% 0.49/0.67      (![X0 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ sk_A @ 
% 0.49/0.67           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.49/0.67           = (k3_xboole_0 @ sk_A @ X0))),
% 0.49/0.67      inference('demod', [status(thm)], ['8', '9'])).
% 0.49/0.67  thf('11', plain,
% 0.49/0.67      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.49/0.67         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['1', '10'])).
% 0.49/0.67  thf(t47_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('12', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.49/0.67           = (k4_xboole_0 @ X11 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf('13', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.49/0.67         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.49/0.67  thf('14', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.49/0.67           = (k4_xboole_0 @ X11 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf('15', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.49/0.67         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.49/0.67      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.67  thf('16', plain,
% 0.49/0.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.49/0.67           = (k3_xboole_0 @ X18 @ 
% 0.49/0.67              (k4_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X20))))),
% 0.49/0.67      inference('demod', [status(thm)], ['5', '6'])).
% 0.49/0.67  thf('17', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.49/0.67           = (k4_xboole_0 @ X11 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf('18', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.49/0.67           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 0.49/0.67      inference('sup+', [status(thm)], ['16', '17'])).
% 0.49/0.67  thf('19', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.49/0.67           = (k4_xboole_0 @ X11 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf('20', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 0.49/0.67      inference('demod', [status(thm)], ['18', '19'])).
% 0.49/0.67  thf('21', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.49/0.67         = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['15', '20'])).
% 0.49/0.67  thf('22', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.49/0.67           = (k4_xboole_0 @ X11 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf(t39_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('23', plain,
% 0.49/0.67      (![X6 : $i, X7 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.49/0.67           = (k2_xboole_0 @ X6 @ X7))),
% 0.49/0.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.49/0.67  thf('24', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['22', '23'])).
% 0.49/0.67  thf(commutativity_k2_xboole_0, axiom,
% 0.49/0.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.49/0.67  thf('25', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.49/0.67  thf('26', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['24', '25'])).
% 0.49/0.67  thf(t51_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.49/0.67       ( A ) ))).
% 0.49/0.67  thf('27', plain,
% 0.49/0.67      (![X21 : $i, X22 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.49/0.67           = (X21))),
% 0.49/0.67      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.49/0.67  thf('28', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.67  thf('29', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.49/0.67  thf(t40_xboole_1, axiom,
% 0.49/0.67    (![A:$i,B:$i]:
% 0.49/0.67     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.49/0.67  thf('30', plain,
% 0.49/0.67      (![X9 : $i, X10 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.49/0.67           = (k4_xboole_0 @ X9 @ X10))),
% 0.49/0.67      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.49/0.67  thf('31', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.49/0.67           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.49/0.67  thf('32', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X0 @ X0)
% 0.49/0.67           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['28', '31'])).
% 0.49/0.67  thf('33', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.67  thf('34', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.49/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('35', plain,
% 0.49/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['33', '34'])).
% 0.49/0.67  thf(t2_boole, axiom,
% 0.49/0.67    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.67  thf('36', plain,
% 0.49/0.67      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.67  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.49/0.67  thf('38', plain,
% 0.49/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.49/0.67         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.49/0.67           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.49/0.67      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.49/0.67  thf('39', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['32', '37', '38'])).
% 0.49/0.67  thf('40', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.49/0.67           = (k4_xboole_0 @ X11 @ X12))),
% 0.49/0.67      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.49/0.67  thf('41', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.49/0.67           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.49/0.67      inference('sup+', [status(thm)], ['39', '40'])).
% 0.49/0.67  thf('42', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.49/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.67  thf('43', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.49/0.67      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.67  thf('44', plain,
% 0.49/0.67      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)) = (sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['21', '43'])).
% 0.49/0.67  thf('45', plain,
% 0.49/0.67      (![X6 : $i, X7 : $i]:
% 0.49/0.67         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.49/0.67           = (k2_xboole_0 @ X6 @ X7))),
% 0.49/0.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.49/0.67  thf('46', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.49/0.67           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.49/0.67  thf('47', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.49/0.67           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['45', '46'])).
% 0.49/0.67  thf('48', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.49/0.67           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.49/0.67  thf('49', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.49/0.67           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 0.49/0.67      inference('demod', [status(thm)], ['47', '48'])).
% 0.49/0.67  thf('50', plain,
% 0.49/0.67      (![X13 : $i, X14 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.49/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.49/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.67  thf('51', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.49/0.67           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('sup+', [status(thm)], ['49', '50'])).
% 0.49/0.67  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.49/0.67  thf('53', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('demod', [status(thm)], ['51', '52'])).
% 0.49/0.67  thf('54', plain,
% 0.49/0.67      (![X2 : $i, X4 : $i]:
% 0.49/0.67         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.49/0.67      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.49/0.67  thf('55', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.67          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.67  thf('56', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.49/0.67      inference('simplify', [status(thm)], ['55'])).
% 0.49/0.67  thf('57', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.49/0.67      inference('sup+', [status(thm)], ['44', '56'])).
% 0.49/0.67  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.49/0.67  
% 0.49/0.67  % SZS output end Refutation
% 0.49/0.67  
% 0.49/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
