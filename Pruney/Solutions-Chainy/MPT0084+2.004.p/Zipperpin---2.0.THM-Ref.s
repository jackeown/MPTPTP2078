%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJybPJQPd5

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:19 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 126 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   22
%              Number of atoms          :  632 ( 921 expanded)
%              Number of equality atoms :   66 (  94 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['14','46'])).

thf('48',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup+',[status(thm)],['13','54'])).

thf('56',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','59'])).

thf('61',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('64',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BJybPJQPd5
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.71  % Solved by: fo/fo7.sh
% 0.44/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.71  % done 639 iterations in 0.255s
% 0.44/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.71  % SZS output start Refutation
% 0.44/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.71  thf(t77_xboole_1, conjecture,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.44/0.71          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.44/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.71        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.44/0.71             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.44/0.71    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.44/0.71  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(d7_xboole_0, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.71       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.71  thf('2', plain,
% 0.44/0.71      (![X2 : $i, X3 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.44/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.71  thf('3', plain,
% 0.44/0.71      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.71  thf(t16_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.71       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.71  thf('4', plain,
% 0.44/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.44/0.71           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.44/0.71  thf(t48_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.71  thf('5', plain,
% 0.44/0.71      (![X18 : $i, X19 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.71           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.71  thf(l32_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.71  thf('6', plain,
% 0.44/0.71      (![X5 : $i, X6 : $i]:
% 0.44/0.71         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.44/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.71  thf('7', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.44/0.71          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.71  thf('8', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.44/0.71          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.44/0.71             (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['4', '7'])).
% 0.44/0.71  thf(t49_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.44/0.71       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.44/0.71  thf('9', plain,
% 0.44/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.44/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 0.44/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.44/0.71  thf('10', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.44/0.71          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.44/0.71             (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.44/0.71      inference('demod', [status(thm)], ['8', '9'])).
% 0.44/0.71  thf('11', plain,
% 0.44/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.71        | (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.44/0.71           (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.44/0.71      inference('sup-', [status(thm)], ['3', '10'])).
% 0.44/0.71  thf('12', plain,
% 0.44/0.71      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.44/0.71        (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.44/0.71      inference('simplify', [status(thm)], ['11'])).
% 0.44/0.71  thf('13', plain,
% 0.44/0.71      (![X18 : $i, X19 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.71           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.71  thf(commutativity_k2_xboole_0, axiom,
% 0.44/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.44/0.71  thf('14', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.44/0.71  thf(t7_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.71  thf('15', plain,
% 0.44/0.71      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 0.44/0.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.71  thf('16', plain,
% 0.44/0.71      (![X5 : $i, X7 : $i]:
% 0.44/0.71         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.44/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.71  thf('17', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.71  thf('18', plain,
% 0.44/0.71      (![X18 : $i, X19 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.71           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.71  thf('19', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.44/0.71           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.44/0.71      inference('sup+', [status(thm)], ['17', '18'])).
% 0.44/0.71  thf(t3_boole, axiom,
% 0.44/0.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.71  thf('20', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.71  thf('21', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.44/0.71      inference('demod', [status(thm)], ['19', '20'])).
% 0.44/0.71  thf('22', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('23', plain,
% 0.44/0.71      (![X5 : $i, X7 : $i]:
% 0.44/0.71         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.44/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.71  thf('24', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.71  thf('25', plain,
% 0.44/0.71      (![X18 : $i, X19 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.71           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.71  thf('26', plain,
% 0.44/0.71      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.44/0.71  thf('27', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.71  thf('28', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.44/0.71  thf('29', plain,
% 0.44/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.44/0.71           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.44/0.71  thf('30', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ sk_A @ X0)
% 0.44/0.71           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.44/0.71      inference('sup+', [status(thm)], ['28', '29'])).
% 0.44/0.71  thf('31', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0))
% 0.44/0.71           = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.71      inference('sup+', [status(thm)], ['21', '30'])).
% 0.44/0.71  thf('32', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 0.44/0.71      inference('demod', [status(thm)], ['26', '27'])).
% 0.44/0.71  thf('33', plain,
% 0.44/0.71      (![X0 : $i]: ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)) = (sk_A))),
% 0.44/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.71  thf('34', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.44/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.71  thf('35', plain,
% 0.44/0.71      (![X18 : $i, X19 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.44/0.71           = (k3_xboole_0 @ X18 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.71  thf('36', plain,
% 0.44/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.71      inference('sup+', [status(thm)], ['34', '35'])).
% 0.44/0.71  thf(t2_boole, axiom,
% 0.44/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.71  thf('37', plain,
% 0.44/0.71      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.71  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.71      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.71  thf('39', plain,
% 0.44/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.71         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.44/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 0.44/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.44/0.71  thf('40', plain,
% 0.44/0.71      (![X5 : $i, X6 : $i]:
% 0.44/0.71         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.44/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.71  thf('41', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.44/0.71          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.71  thf('42', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.44/0.71          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['38', '41'])).
% 0.44/0.71  thf('43', plain,
% 0.44/0.71      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.44/0.71  thf('44', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.71          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['42', '43'])).
% 0.44/0.71  thf('45', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.44/0.71      inference('simplify', [status(thm)], ['44'])).
% 0.44/0.71  thf('46', plain,
% 0.44/0.71      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ X0))),
% 0.44/0.71      inference('sup+', [status(thm)], ['33', '45'])).
% 0.44/0.71  thf('47', plain,
% 0.44/0.71      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))),
% 0.44/0.71      inference('sup+', [status(thm)], ['14', '46'])).
% 0.44/0.71  thf('48', plain,
% 0.44/0.71      (![X5 : $i, X7 : $i]:
% 0.44/0.71         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.44/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.71  thf('49', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.71  thf(t41_xboole_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.71       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.44/0.71  thf('50', plain,
% 0.44/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.44/0.71           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.44/0.71  thf('51', plain,
% 0.44/0.71      (![X5 : $i, X6 : $i]:
% 0.44/0.71         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.71  thf('52', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.54/0.71          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.71  thf('53', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         (((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.71          | (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_C))),
% 0.54/0.71      inference('sup-', [status(thm)], ['49', '52'])).
% 0.54/0.71  thf('54', plain,
% 0.54/0.71      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.54/0.71      inference('simplify', [status(thm)], ['53'])).
% 0.54/0.71  thf('55', plain,
% 0.54/0.71      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_C)),
% 0.54/0.71      inference('sup+', [status(thm)], ['13', '54'])).
% 0.54/0.71  thf('56', plain,
% 0.54/0.71      (![X5 : $i, X7 : $i]:
% 0.54/0.71         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.54/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.71  thf('57', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['55', '56'])).
% 0.54/0.71  thf('58', plain,
% 0.54/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.54/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 0.54/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.54/0.71  thf('59', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)) = (k1_xboole_0))),
% 0.54/0.71      inference('demod', [status(thm)], ['57', '58'])).
% 0.54/0.71  thf('60', plain, ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.54/0.71      inference('demod', [status(thm)], ['12', '59'])).
% 0.54/0.71  thf('61', plain,
% 0.54/0.71      (![X5 : $i, X7 : $i]:
% 0.54/0.71         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.54/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.71  thf('62', plain,
% 0.54/0.71      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.54/0.71         = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.71  thf('63', plain,
% 0.54/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.54/0.71           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 0.54/0.71      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.54/0.71  thf('64', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.54/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.71  thf('65', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.54/0.71      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.54/0.71  thf('66', plain,
% 0.54/0.71      (![X2 : $i, X4 : $i]:
% 0.54/0.71         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.54/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.71  thf('67', plain,
% 0.54/0.71      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.54/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.54/0.71  thf('68', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.54/0.71      inference('simplify', [status(thm)], ['67'])).
% 0.54/0.71  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
